#!/usr/bin/env python3
"""Compile all 51 local proof sources and the checked audit, sequentially, into new outputs.

Upstream dependencies must already be installed/built. This never builds dependencies.
It rejects any dependency search root containing a prebuilt packaged local module.
"""
import argparse
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def linux_memory(pgid=None):
    if not Path('/proc/meminfo').exists():
        return None, None
    available = int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines()
                         if x.startswith('MemAvailable:')))
    rss = 0
    if pgid is not None:
        for path in Path('/proc').iterdir():
            if not path.name.isdigit():
                continue
            try:
                if os.getpgid(int(path.name)) == pgid:
                    rss += int(next(x.split()[1] for x in (path / 'status').read_text().splitlines()
                                    if x.startswith('VmRSS:')))
            except (OSError, StopIteration):
                pass
    return available, rss


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, help='Pinned Lean 4.32.2 executable')
    parser.add_argument('--dependency-path-file', required=True, type=Path,
                        help='Colon-separated LEAN_PATH containing upstream objects only')
    parser.add_argument('--output', required=True, type=Path, help='New output directory; must not exist')
    parser.add_argument('--memory-mb', type=int, default=3200)
    parser.add_argument('--union-memory-mb', type=int, default=3500)
    parser.add_argument('--module-memory', action='append', default=[], metavar='MODULE=MB',
                        help='Explicit per-module limit, bounded above by --union-memory-mb')
    parser.add_argument('--rss-limit-kib', type=int, default=3879000)
    parser.add_argument('--minimum-available-kib', type=int, default=1048576)
    parser.add_argument('--minimum-disk-bytes', type=int, default=2147483648)
    args = parser.parse_args()
    subprocess.run([sys.executable, str(ROOT / 'scripts/verify_sources.py')], check=True)
    assert not list((ROOT / 'Proofs').rglob('*.olean*')), 'Prebuilt object present in source/cwd tree'
    lean = str(Path(args.lean).resolve())
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.32.2,' in version and 'f3b06c705e6c85f5314019d5d3baab0fec5b580c' in version, version
    manifest = json.loads((ROOT / 'source-manifest.json').read_text())
    records = {r['module']: r for r in manifest['modules']}
    module_memory = {}
    for setting in args.module_memory:
        name, value = setting.split('=', 1)
        limit = int(value)
        assert name in records and name not in module_memory, 'Unknown or repeated module-memory setting'
        assert 0 < limit <= args.union_memory_mb, 'Module-memory setting exceeds union ceiling'
        module_memory[name] = limit
    dependencies = [str(Path(x).resolve()) for x in args.dependency_path_file.read_text().strip().split(os.pathsep) if x]
    assert dependencies, 'No dependency search roots supplied'
    for directory in dependencies:
        assert Path(directory).is_dir(), directory
        for name in records:
            assert not (Path(directory) / (name + '.olean')).exists(), f'Old local proof object visible: {directory}/{name}.olean'
    output = args.output.resolve()
    assert not output.exists(), 'Fresh build requires a nonexistent output directory'
    output.mkdir(parents=True)
    objects, logs = output / 'objects', output / 'logs'
    objects.mkdir()
    logs.mkdir()
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(objects), *dependencies]), LEAN_NUM_THREADS='1')
    # No inherited source path is allowed to inject undeclared source discovery.
    env.pop('LEAN_SRC_PATH', None)
    result = {'status': 'RUNNING', 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'lean_version': version, 'lean_executable': lean, 'lean_path': env['LEAN_PATH'].split(os.pathsep),
              'source_manifest_sha256': digest(ROOT / 'source-manifest.json'),
              'fresh_local_outputs': True, 'old_local_proof_objects_allowed': False,
              'upstream_dependency_builds': 0, 'sequential': True,
              'resource_limits': {'helper_memory_mb': args.memory_mb,
                  'union_memory_mb': args.union_memory_mb, 'module_memory_mb': module_memory, 'threads': 1,
                  'rss_limit_kib': args.rss_limit_kib,
                  'minimum_available_kib': args.minimum_available_kib,
                  'minimum_disk_bytes': args.minimum_disk_bytes,
                  'linux_process_group_sampling': Path('/proc/meminfo').exists(),
                  'sample_interval_seconds': 0.25}, 'records': []}
    report = output / 'build-result.json'
    def save():
        report.write_text(json.dumps(result, indent=2) + '\n')
    save()
    for name in manifest['dependency_order']:
        source = ROOT / records[name]['path']
        source_before = digest(source)
        assert source_before == records[name]['source_sha256']
        memory_mb = args.union_memory_mb if name in {'ScopedPillaiIrreducibility', 'ScopedPillaiAudit'} else args.memory_mb
        memory_mb = module_memory.get(name, memory_mb)
        command = [lean, '-M', str(memory_mb), '-j', '1', '-o', str(objects / (name + '.olean')), source.name]
        available, _ = linux_memory()
        assert available is None or available >= args.minimum_available_kib, 'Low free RAM before build'
        initial_available = available
        minimum_available = available
        initial_disk = shutil.disk_usage(output).free
        minimum_disk = initial_disk
        assert initial_disk >= args.minimum_disk_bytes, 'Low free disk before build'
        started = time.monotonic()
        maximum = 0
        stopped = None
        log = logs / (name + '.log')
        with log.open('w') as handle:
            process = subprocess.Popen(command, cwd=ROOT / 'Proofs', env=env, stdout=handle,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                while process.poll() is None:
                    available, rss = linux_memory(process.pid)
                    maximum = max(maximum, rss or 0)
                    disk = shutil.disk_usage(output).free
                    minimum_disk = min(minimum_disk, disk)
                    if available is not None:
                        minimum_available = min(minimum_available, available)
                    if ((available is not None and available < args.minimum_available_kib)
                            or (rss is not None and rss > args.rss_limit_kib)
                            or disk < args.minimum_disk_bytes):
                        stopped = 'RAM/RSS/disk resource guard'
                        os.killpg(process.pid, signal.SIGTERM)
                        break
                    time.sleep(0.25)
                try:
                    code = process.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    code = process.wait()
            except BaseException:
                os.killpg(process.pid, signal.SIGTERM)
                process.wait()
                raise
        record = {'module': name, 'command': command, 'exit_code': code, 'stopped': stopped,
                  'seconds': round(time.monotonic() - started, 3), 'peak_sampled_rss_kib': maximum,
                  'initial_available_kib': initial_available, 'minimum_sampled_available_kib': minimum_available,
                  'initial_free_disk_bytes': initial_disk, 'minimum_sampled_free_disk_bytes': minimum_disk,
                  'lean_memory_limit_mb': memory_mb, 'source_sha256': source_before,
                  'source_sha256_after': digest(source), 'source_unchanged': source_before == digest(source),
                  'log': str(log), 'log_sha256': digest(log)}
        obj = objects / (name + '.olean')
        if code == 0 and obj.exists():
            record['object_sha256'] = digest(obj)
            record['matches_historical_object_bytes'] = digest(obj) == records[name]['imported_object_sha256']
        result['records'].append(record)
        text = log.read_text()
        if code != 0 or stopped or not record['source_unchanged'] or re.search(r'\b(?:warning|error):', text):
            result['status'] = 'FAILED'
            save()
            raise SystemExit(f'Build failed or unclean diagnostic: {name}; see {log}')
        save()
        print(f'{name}: checked', flush=True)
    audit = (logs / 'ScopedPillaiAudit.log').read_text()
    parsed = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit, flags=re.S)
    expected = json.loads((ROOT / 'expected-roots.json').read_text())
    assert [name for name, _ in parsed] == expected, 'Missing or unexpected audit declarations'
    audits = [{'declaration': name, 'axioms': sorted({x.strip() for x in body.split(',') if x.strip()})}
              for name, body in parsed]
    assert all(set(a['axioms']) <= ALLOWED_AXIOMS for a in audits), 'Unexpected recursive axiom'
    assert all(digest(ROOT / r['path']) == r['source_sha256'] for r in manifest['modules']), 'Source changed during build'
    result.update(status='PASS', completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  production_modules=51, audit_modules=1, audits=audits,
                  note='This is a fresh source elaboration and recursive axiom audit. It is not a new independent export/replay check.')
    save()
    print(f'PASS: all local sources rebuilt; 41 recursive standard-axiom audits. {report}')


if __name__ == '__main__':
    with (ROOT / '.compiler.lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        main()
