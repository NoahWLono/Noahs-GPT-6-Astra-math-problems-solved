#!/usr/bin/env python3
"""Verify exact inputs, then freshly compile every custom module. Python 3.10+."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from unpack_sources import ensure_sources

ROOT = Path(__file__).resolve().parent
MATHLIB_REV = '905b95818eb32af7874a58b427f50c1711a5e96c'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(name):
    return json.loads((ROOT / 'manifests' / name).read_text())

def safe_source(relative):
    path = ROOT / 'source' / relative
    require(not Path(relative).is_absolute() and '..' not in Path(relative).parts,
            'Unsafe source path: ' + relative)
    require(path.is_file() and not path.is_symlink(), 'Missing regular file: ' + relative)
    return path

def inputs():
    modules = read('SOURCE_MANIFEST.json')['modules']
    payloads = read('JSON_MANIFEST.json')['files']
    order = read('BUILD_ORDER.json')['ordered_modules']
    axioms = read('AXIOM_REQUIREMENTS.json')['modules']
    require(len(modules) == 3046 and len(payloads) == 1444, 'Unexpected input counts')
    by_name = {entry['module']: entry for entry in modules}
    require(len(by_name) == len(modules) and len(order) == len(modules), 'Duplicate module')
    files = set()
    for entry in modules + payloads:
        path = safe_source(entry['path'])
        require(path.stat().st_size == entry['bytes'] and digest(path) == entry['sha256'],
                'Source hash mismatch: ' + entry['path'])
        require(entry['path'] not in files, 'Duplicate path')
        files.add(entry['path'])
    actual = {str(p.relative_to(ROOT / 'source')) for p in (ROOT / 'source').rglob('*') if p.is_file()}
    require(files == actual, 'Unlisted or missing files in source directory')
    seen = set()
    external = {'Lean', 'Std', 'Std.Sat.CNF.Basic', 'Mathlib.Data.Fintype.Card',
                'Mathlib.Data.Nat.Find', 'Mathlib.Logic.Equiv.Fintype'}
    for name in order:
        require(name in by_name and name not in seen, 'Invalid build order')
        entry = by_name[name]
        require(entry['path'] == name.replace('.', '/') + '.lean', 'Module path mismatch')
        require(all(dep in seen or dep in external for dep in entry['imports']),
                'Unresolved or out-of-order import: ' + name)
        seen.add(name)
    require(seen == set(by_name), 'Incomplete build order')
    for name, audit in axioms.items():
        require(name in by_name and audit['source_sha256'] == by_name[name]['sha256']
                and audit['expected_theorems'], 'Invalid named audit requirement')
    return by_name, order, axioms

def parse_audits(text, expected):
    audits = [(name, [a.strip() for a in values.split(',') if a.strip()])
              for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text, re.S)]
    audits += [(name, []) for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    require(set(expected) <= {name for name, _ in audits}, 'Missing expected named axiom audit')
    require(all(set(values) <= ALLOWED for _, values in audits), 'Nonstandard axiom reported')
    return [{'theorem': name, 'axioms': values} for name, values in audits]

def output(command, cwd=None, env=None):
    return subprocess.check_output(command, cwd=cwd, env=env, text=True).strip()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-inputs', action='store_true', help='Static hashes/order only; never runs Lean')
    parser.add_argument('--smoke-test', action='store_true', help='Compile a fixed small closure only; never verifies the final theorem')
    parser.add_argument('--lean-root', type=Path, help='Official Lean 4.32.2 installation directory')
    parser.add_argument('--mathlib', type=Path, help='Prepared Mathlib checkout at pinned revision')
    parser.add_argument('--output', type=Path, default=ROOT / '.verify', help='New output directory; must not exist')
    args = parser.parse_args()
    ensure_sources()
    modules, order, requirements = inputs()
    if args.check_inputs:
        print(json.dumps({'input_integrity': 'passed', 'modules': len(order), 'quoted_json': 1444,
                          'compiler_invoked': False}))
        return
    require(args.lean_root is not None and args.mathlib is not None, 'Provide --lean-root and --mathlib')
    tc, ml, dest = args.lean_root.resolve(), args.mathlib.resolve(), args.output.resolve()
    require(not dest.exists(), 'Output directory must be new; no imported proof objects are accepted')
    require(not dest.is_relative_to(ROOT / 'source'), 'Output cannot be inside proof sources')
    lean = tc / 'bin' / 'lean'
    version = output([str(lean), '--version'])
    require(re.search(r'Lean \(version 4\.32\.2(?:,|\))', version) is not None, 'Wrong Lean version: ' + version)
    require(output(['git', '-C', str(ml), 'rev-parse', 'HEAD']) == MATHLIB_REV, 'Wrong Mathlib revision')
    require(not output(['git', '-C', str(ml), 'status', '--porcelain', '--untracked-files=no']),
            'Tracked Mathlib files are modified')
    require(digest(ml / 'lake-manifest.json') == digest(ROOT / 'manifests/mathlib-lake-manifest.json'),
            'Mathlib dependency lock differs')
    require((ml / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.32.2', 'Wrong dependency toolchain')
    deps = json.loads((ml / 'lake-manifest.json').read_text())['packages']
    paths = [dest / 'objects', tc / 'lib/lean', ml / '.lake/build/lib/lean']
    for dep in deps:
        package = ml / '.lake/packages' / dep['name']
        require(dep['type'] == 'git', 'Unsupported dependency kind')
        require(output(['git', '-C', str(package), 'rev-parse', 'HEAD']) == dep['rev'],
                'Wrong dependency revision: ' + dep['name'])
        require(not output(['git', '-C', str(package), 'status', '--porcelain', '--untracked-files=no']),
                'Tracked dependency files are modified: ' + dep['name'])
        paths.append(package / '.lake/build/lib/lean')
    dest.mkdir(parents=True)
    (dest / 'objects').mkdir()
    (dest / 'logs').mkdir()
    env = dict(os.environ, LEAN_SYSROOT=str(tc), LEAN_PATH=os.pathsep.join(map(str, paths)),
               OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1')
    receipts = []
    full_count = len(order)
    if args.smoke_test:
        selected = set()
        def include(name):
            if name in selected:
                return
            selected.add(name)
            for dependency in modules[name]['imports']:
                if dependency in modules:
                    include(dependency)
        include('BergeMod.K1.Replay0000')
        include('Q7Mod.Canonical.BergeEightNormalization')
        order = [name for name in order if name in selected]
    for index, name in enumerate(order, 1):
        entry = modules[name]
        source = safe_source(entry['path'])
        require(digest(source) == entry['sha256'], 'Input changed during build')
        target = dest / 'objects' / Path(entry['path']).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), '-j1', '-DmaxErrors=1', '-o', str(target), str(source)]
        run = subprocess.run(command, cwd=ROOT / 'source', env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True)
        log = dest / 'logs' / (name + '.log')
        log.write_text(run.stdout)
        require(run.returncode == 0 and target.is_file(), 'Compilation failed: ' + name + '; inspect ' + str(log))
        require(not any(term in run.stdout for term in ['sorryAx', 'Lean.ofReduceBool',
                "declaration uses 'sorry'", 'error:']), 'Untrusted result in ' + name)
        audits = parse_audits(run.stdout, requirements.get(name, {}).get('expected_theorems', []))
        receipts.append({'module': name, 'source_sha256': entry['sha256'],
                         'olean_sha256': digest(target), 'log_sha256': digest(log), 'axiom_audits': audits})
        (dest / 'PROGRESS.json').write_text(json.dumps({'completed': index, 'total': len(order), 'last': name}) + '\n')
        print(f'[{index}/{len(order)}] {name}', flush=True)
    inputs()  # Detect source/data changes during the run.
    if args.smoke_test:
        (dest / 'SMOKE_RESULT.json').write_text(json.dumps({
            'status': 'fixed smoke subset freshly compiled; final theorem NOT verified',
            'lean_version': version, 'mathlib_revision': MATHLIB_REV,
            'full_closure_module_count': full_count, 'compiled_subset_count': len(order),
            'modules': receipts, 'final_theorem_verified': False}, indent=2) + '\n')
        print(f'Smoke subset ({len(order)} modules) passed; final theorem was NOT verified.')
        return
    (dest / 'RESULT.json').write_text(json.dumps({'status': 'all custom modules freshly compiled',
        'lean_version': version, 'mathlib_revision': MATHLIB_REV, 'modules': receipts,
        'exact_type_audit_module': 'Q7Mod.Integration.ExactQ7Audit',
        'theorem': 'ExactCubeCodes.localIdentifying_Q7_optimum24'}, indent=2) + '\n')
    print('All 3,046 custom modules freshly compiled; exact-type and named axiom audits passed.')

if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, subprocess.CalledProcessError) as exc:
        print('Verification failed: ' + str(exc), file=sys.stderr)
        sys.exit(1)
