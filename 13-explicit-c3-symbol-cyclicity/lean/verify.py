#!/usr/bin/env python3
"""Verify the exact source transport; optionally rebuild all project modules.
Only Python's standard library is required. No existing project object is reused.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tarfile
import time

ROOT = Path(__file__).resolve().parent

def digest(data):
    return hashlib.sha256(data).hexdigest()

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def check_sources():
    pins = json.loads((ROOT / 'pins.json').read_text())
    raw = (ROOT / 'SOURCE_SHA256SUMS').read_bytes()
    require(digest(raw) == pins['source_manifest_sha256'], 'Source manifest hash mismatch')
    expected = dict(line.split('  ', 1)[::-1] for line in raw.decode().splitlines())
    require(len(expected) == pins['source_count'], 'Source count mismatch')
    archive = ROOT / 'sources.tar.gz'
    require(digest(archive.read_bytes()) == pins['archive_sha256'], 'Archive hash mismatch')
    sources = {}
    with tarfile.open(archive, 'r:gz') as tf:
        for member in tf:
            path = PurePosixPath(member.name)
            require(member.isfile() and not path.is_absolute() and '..' not in path.parts,
                    'Unsafe archive member: ' + member.name)
            require(member.name in expected and member.name not in sources,
                    'Unexpected or duplicate member: ' + member.name)
            require(member.size <= pins['source_bytes'], 'Oversized archive member')
            data = tf.extractfile(member).read()
            require(digest(data) == expected[member.name], 'Source hash mismatch: ' + member.name)
            sources[member.name] = data
    require(set(sources) == set(expected), 'Missing source member')
    require(sum(map(len, sources.values())) == pins['source_bytes'], 'Source byte count mismatch')
    order = (ROOT / 'build-order.txt').read_text().splitlines()
    modules = {p[4:-5].replace('/', '.'): data for p, data in sources.items()}
    require(len(order) == len(modules) and set(order) == set(modules), 'Build order mismatch')
    seen = set()
    imported = json.loads((ROOT / 'imports.json').read_text())
    external = set()
    for mod in order:
        im = re.findall(r'^\s*(?:(?:public|meta|private)\s+)*import\s+([A-Za-z0-9_.]+)',
                        modules[mod].decode(), re.M)
        require(im == imported['local'][mod], 'Import manifest mismatch: ' + mod)
        for dep in im:
            if dep in modules:
                require(dep in seen, 'Dependency order violation: ' + dep)
            else:
                require(dep.startswith('Mathlib.'), 'Unexpected external import: ' + dep)
                external.add(dep)
        seen.add(mod)
    require(external == set(imported['external']), 'External import list mismatch')
    require(order[-1] == 'FinalAudit', 'Final audit is not last')
    for mod in ['FinalAssembly', 'FinalAudit', 'FamilyInterface', 'SupportingEndpoint']:
        require((ROOT / (mod + '.lean')).read_bytes() == modules[mod], 'Readable copy mismatch: ' + mod)
    print('PASS: 763 exact sources, archive safety, hashes, import order and readable copies.')
    return pins, sources, order

def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()

def check_dependencies(pins, mathlib, lean):
    require(git(mathlib, 'rev-parse', 'HEAD') == pins['mathlib_revision'], 'Mathlib revision mismatch')
    require(not git(mathlib, 'status', '--porcelain', '--untracked-files=no'), 'Modified tracked Mathlib files')
    require(digest((mathlib / 'lake-manifest.json').read_bytes()) == pins['mathlib_manifest_sha256'],
            'Mathlib dependency lock mismatch')
    require((mathlib / 'lean-toolchain').read_text().strip() == pins['lean_toolchain'], 'Toolchain pin mismatch')
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    require(re.search(r'Lean \(version 4\.32\.2(?:,|\s)', version), 'Wrong Lean version: ' + version)
    lock = json.loads((ROOT / 'mathlib-lake-manifest.json').read_text())
    roots = [mathlib / '.lake/build/lib/lean']
    for package in lock['packages']:
        path = mathlib / '.lake/packages' / package['name']
        require(git(path, 'rev-parse', 'HEAD') == package['rev'], 'Dependency revision mismatch: ' + package['name'])
        require(not git(path, 'status', '--porcelain', '--untracked-files=no'), 'Modified dependency: ' + package['name'])
        obj = path / '.lake/build/lib/lean'
        if obj.is_dir():
            roots.append(obj)
    require(roots[0].is_dir(), 'Build pinned Mathlib dependencies first')
    for mod in json.loads((ROOT / 'imports.json').read_text())['external']:
        require((roots[0] / (mod.replace('.', '/') + '.olean')).is_file(), 'Missing upstream object: ' + mod)
    print('PASS: official version number, pinned Mathlib and all eight dependency revisions.')
    return roots, version

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check-only', action='store_true', help='Verify archive and source manifests only; no compiler')
    ap.add_argument('--check-dependencies-only', action='store_true')
    ap.add_argument('--mathlib', type=Path, help='Pinned, built Mathlib checkout')
    ap.add_argument('--lean', type=Path, help='Official Lean 4.32.2 executable')
    ap.add_argument('--output', type=Path, default=ROOT / '.build', help='NEW output directory; must not exist')
    ap.add_argument('--timeout', type=int, default=300, help='Wall seconds per compiler invocation')
    args = ap.parse_args()
    pins, sources, order = check_sources()
    if args.check_only:
        return
    require(args.mathlib is not None and args.lean is not None, 'Supply --mathlib and --lean')
    mathlib, lean = args.mathlib.resolve(), args.lean.resolve()
    roots, version = check_dependencies(pins, mathlib, lean)
    if args.check_dependencies_only:
        return
    output = args.output.absolute()
    require(not output.exists() and not output.is_symlink(), 'Output must be a new nonexistent directory')
    require(args.timeout > 0, 'Timeout must be positive')
    require(shutil.disk_usage(output.parent).free >= 2 * 1024**3, 'Need at least 2 GiB free disk for custom build')
    output.mkdir()
    src, obj, logs = output / 'src', output / 'lean', output / 'logs'
    for path, data in sources.items():
        p = output / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)
    obj.mkdir(); logs.mkdir()
    env = dict(os.environ)
    env['LEAN_PATH'] = os.pathsep.join(map(str, [obj, *roots]))
    env.pop('LEAN_SRC_PATH', None)
    receipts = []
    for index, mod in enumerate(order, 1):
        relative = mod.replace('.', '/')
        target = obj / (relative + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        log = logs / (mod + '.txt')
        with log.open('wb') as stream:
            result = subprocess.run([str(lean), '-j1', relative + '.lean', '-o', str(target)],
                                    cwd=src, env=env, stdout=stream, stderr=subprocess.STDOUT,
                                    timeout=args.timeout, check=False)
        receipt = {'module': mod, 'exit_code': result.returncode, 'wall_seconds': time.monotonic()-start,
                   'source_sha256': digest(sources['src/' + relative + '.lean']),
                   'log_sha256': digest(log.read_bytes())}
        receipts.append(receipt)
        (output / 'receipts.json').write_text(json.dumps(receipts, indent=2) + '\n')
        require(result.returncode == 0 and target.is_file(), 'Compile failed: ' + mod + '; inspect logs')
        print(f'{index}/{len(order)} {mod}', flush=True)
    audit = (logs / 'FinalAudit.txt').read_text()
    expected = "'PrimeFiveFamily.symbolFamily_cyclicity' depends on axioms:"
    require(expected in audit, 'Missing final named axiom audit')
    axiom_entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit, re.S)
    required_names = {
        'PrimeFiveFamily.fifthScalar', 'PrimeFiveFamily.frozenNumerator_fifth',
        'PrimeFiveFamily.symbolFamily_cyclicity', 'PrimeCyclicity.N5Modern.numerator_fifth',
        'FrozenCentralOutput75.candidateOutput75_support',
        'ConcreteCoordinateBridge.evalLaurent_scalar_of_support',
        'PrimeFiveFamily.supporting_cyclicity_of_fifthPower_identity'}
    require(len(axiom_entries) == 7 and {name for name, _ in axiom_entries} == required_names,
            'Missing or unexpected final named axiom reports')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in axiom_entries:
        normalized = re.sub(r'\.\{[^}]*\}', '', axioms)
        actual = set(x.strip() for x in normalized.split(',') if x.strip())
        require(actual <= allowed, 'Nonstandard axiom: ' + name)
        if name == 'PrimeFiveFamily.symbolFamily_cyclicity':
            require(actual == allowed, 'Final axiom set differs from recorded set')
    require("'PrimeFiveFamily.fifthOutput_eq_candidate' does not depend on any axioms" in audit,
            'Missing axiom-free output alignment audit')
    result = {'status': 'passed', 'modules': len(order), 'reused_project_objects': 0,
              'lean_version': version, 'mathlib_revision': pins['mathlib_revision'],
              'final_axioms': sorted(allowed), 'source_archive_sha256': pins['archive_sha256']}
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: fresh project build and required final axiom audits.')

if __name__ == '__main__':
    main()
