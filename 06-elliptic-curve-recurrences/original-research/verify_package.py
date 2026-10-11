#!/usr/bin/env python3
"""Check artifact integrity and rerun the exact, bounded ASTRA-01 experiments.

Standard library only for core checks. Optional symbolic checks need SymPy.
No network requests. The shipped results are never overwritten.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


def check_manifest(root: Path) -> int:
    manifest = root / 'SHA256SUMS'
    require(manifest.is_file(), 'Missing SHA256SUMS')
    listed = set()
    for line in manifest.read_text(encoding='utf-8').splitlines():
        if not line:
            continue
        expected, name = line.split('  ', 1)
        rel = PurePosixPath(name)
        require(not rel.is_absolute() and '..' not in rel.parts,
                'Unsafe manifest path')
        require(name not in listed, 'Duplicate manifest entry')
        listed.add(name)
        path = root.joinpath(*rel.parts)
        require(path.is_file() and not path.is_symlink(), f'Missing or nonregular file: {name}')
        observed = hashlib.sha256(path.read_bytes()).hexdigest()
        require(observed == expected, f'Checksum mismatch: {name}')
    require(all(name in listed for name in (
        'manuscript.pdf', 'manuscript.tex', 'verify_package.py',
        'src/experiments.py', 'src/independent_check.py',
        'results/experiments.json', 'results/independent_checks.json')),
        'Manifest omits a required file')
    return len(listed)


def mathematical_content(value):
    """Ignore measurements that are not part of a mathematical certificate."""
    if isinstance(value, dict):
        return {k: mathematical_content(v) for k, v in value.items()
                if k not in {'runtime_seconds_diagnostic_only', 'sympy_version'}}
    if isinstance(value, list):
        return [mathematical_content(v) for v in value]
    return value


def compare_json(original: Path, regenerated: Path) -> None:
    expected = mathematical_content(json.loads(original.read_text()))
    actual = mathematical_content(json.loads(regenerated.read_text()))
    require(expected == actual, f'Reproduced mathematical result differs: {original.name}')


def execute(script: Path, cwd: Path) -> str:
    completed = subprocess.run(
        [sys.executable, '-B', str(script)], cwd=cwd, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=45, check=False,
    )
    require(completed.returncode == 0,
            f'{script.name} failed with exit {completed.returncode}:\n{completed.stdout}')
    return completed.stdout


def main() -> None:
    require(sys.version_info >= (3, 10), 'Python 3.10 or later is required')
    root = Path(__file__).resolve().parent
    count = check_manifest(root)
    print(f'PASS: SHA-256 integrity for {count} shipped files.')
    with tempfile.TemporaryDirectory(prefix='astra01-reproduction-') as folder:
        work = Path(folder)
        (work/'src').mkdir()
        (work/'results').mkdir()
        for name in ('experiments.py', 'independent_check.py', 'symbolic_check.py'):
            shutil.copyfile(root/'src'/name, work/'src'/name)
        for script, result in (
            ('experiments.py', 'experiments.json'),
            ('independent_check.py', 'independent_checks.json'),
        ):
            execute(work/'src'/script, work)
            compare_json(root/'results'/result, work/'results'/result)
            print(f'PASS: {script}; exact mathematical output reproduced.')
        if importlib.util.find_spec('sympy') is None:
            symbolic_status = 'SKIPPED: SymPy not installed'
            print(symbolic_status)
        else:
            execute(work/'src'/'symbolic_check.py', work)
            compare_json(root/'results'/'symbolic_checks.json',
                         work/'results'/'symbolic_checks.json')
            symbolic_status = 'PASS'
            print('PASS: symbolic_check.py; polynomial identities reproduced.')
        data = json.loads((work/'results'/'experiments.json').read_text())
        independently = json.loads((work/'results'/'independent_checks.json').read_text())
        print(json.dumps({
            'status': 'PASS',
            'synthetic_only': data['synthetic_only'],
            'totals': data['totals'],
            'independent_all_pairs_group_law_checks': independently['all_pairs_group_law_checks'],
            'symbolic_status': symbolic_status,
            'external_peer_review': False,
            'formal_proof_assistant_verification': False,
            'original_results_unchanged': True,
        }, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        sys.exit(1)
