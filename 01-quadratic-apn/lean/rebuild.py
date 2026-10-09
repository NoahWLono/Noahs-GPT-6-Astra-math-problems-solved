#!/usr/bin/env python3
"""Rebuild every local proof from frozen source, then print the endpoint audit.
Run: lake update && lake exe cache get && python3 rebuild.py
No original local compiled proofs or machine-specific paths are used.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
PIN = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'


def source_check():
    manifest = json.loads((ROOT / 'source-manifest.json').read_text())
    order = (ROOT / 'build-order.txt').read_text().splitlines()
    if [r['module'] for r in manifest] != order or len(set(order)) != len(order):
        raise RuntimeError('Manifest and build order disagree')
    known = set(order)
    done = set()
    for row in manifest:
        path = ROOT / row['path']
        if row['path'] != row['module'].replace('.', '/') + '.lean':
            raise RuntimeError('Unexpected source path')
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != row['sha256']:
            raise RuntimeError('Source hash mismatch: ' + row['path'])
        # Imports in this frozen package are single-line declarations.
        for line in data.decode().splitlines():
            if line.startswith('import '):
                for dep in line.split()[1:]:
                    if dep in known and dep not in done:
                        raise RuntimeError('Dependency order violation: ' + dep)
        done.add(row['module'])
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*.lean')
              if not any(part in {'.lake', 'build'} for part in p.relative_to(ROOT).parts)
              and p.name != 'lakefile.lean'}
    if actual != {r['path'] for r in manifest}:
        raise RuntimeError('Unexpected or missing local proof modules')
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only', action='store_true', help='Check source hashes and local dependency order only')
    parser.add_argument('--timeout', type=int, default=600, help='Seconds allowed per module; default 600')
    args = parser.parse_args()
    rows = source_check()
    print(f'Checked {len(rows)} local source hashes and build order.', flush=True)
    if args.check_only:
        return
    dep = ROOT / '.lake/packages/mathlib'
    commit = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], text=True).strip()
    if commit != PIN:
        raise RuntimeError('Wrong mathlib commit; run lake update')
    clean_env = os.environ.copy()
    clean_env.pop('LEAN_PATH', None)
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT, env=clean_env, text=True).strip()
    if not re.search(r'\bversion 4\.19\.0\b', version):
        raise RuntimeError('Wrong Lean version: ' + version)
    lean = subprocess.check_output(['lake', 'env', 'which', 'lean'], cwd=ROOT, env=clean_env, text=True).strip()
    raw = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, env=clean_env, text=True).strip()
    # Only Lake-managed dependencies survive; no local .lake/build/lib/lean.
    packages = Path(os.path.abspath(ROOT / '.lake/packages'))
    libs = []
    for part in raw.split(os.pathsep):
        if not part:
            continue
        path = Path(part)
        path = Path(os.path.abspath(ROOT / path)) if not path.is_absolute() else Path(os.path.abspath(path))
        if path.is_relative_to(packages):
            libs.append(str(path))
    if not libs:
        raise RuntimeError('No Lake dependency libraries found; run lake exe cache get')
    out = ROOT / 'build'
    if out.exists():
        shutil.rmtree(out)  # Generated output only; checked-in source is never removed.
    objects = out / 'lean'
    logs = out / 'logs'
    objects.mkdir(parents=True)
    logs.mkdir()
    env = clean_env.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(objects)] + libs)
    env['MALLOC_ARENA_MAX'] = '2'
    (out / 'environment.json').write_text(json.dumps({'lean': version, 'mathlib_commit': commit,
        'scope': 'All local sources rebuilt; upstream toolchain and cached mathlib libraries reused'}, indent=2) + '\n')
    results = []
    for i, row in enumerate(rows, 1):
        name = row['module']
        dest = objects / (name.replace('.', '/') + '.olean')
        dest.parent.mkdir(parents=True, exist_ok=True)
        print(f'[{i}/{len(rows)}] {name}', flush=True)
        start = time.monotonic()
        with (logs / (name + '.log')).open('w') as log:
            result = subprocess.run([lean, '--root=' + str(ROOT), '-j1', '-s8192', '-o', str(dest),
                                     str(ROOT / row['path'])], cwd=ROOT, env=env,
                                    stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
        results.append({'module': name, 'exit': result.returncode, 'seconds': round(time.monotonic()-start, 3)})
        (out / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        if result.returncode:
            print((logs / (name + '.log')).read_text(), file=sys.stderr)
            raise RuntimeError('Compilation failed: ' + name)
    (out / 'SUCCESS').write_text(f'All {len(rows)} local modules freshly compiled.\n')
    print((logs / 'APNEightFinalAudit.log').read_text())
    print('SUCCESS: entire local dependency closure and endpoint audit rebuilt.')


if __name__ == '__main__':
    main()
