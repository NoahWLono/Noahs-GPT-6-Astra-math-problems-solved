#!/usr/bin/env python3
"""Read-only check of installed dependency commits and imported source bytes."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packages', type=Path, default=ROOT / '.lake/packages')
    args = parser.parse_args()
    packages = args.packages.resolve()
    lock = json.loads((ROOT / 'lake-manifest.json').read_text())
    for package in lock['packages']:
        path = packages / package['name']
        actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        assert actual == package['rev'], f'Commit mismatch: {package["name"]}: {actual}'
    records = json.loads((ROOT / 'upstream-source-hashes.json').read_text())
    count = 0
    for rec in records:
        actual = packages / rec['path']
        assert hashlib.sha256(actual.read_bytes()).hexdigest() == rec['sha256'], rec['module']
        count += 1
    assert count == 2979
    print(f'PASS: {len(lock["packages"])} locked package revisions and {count} imported upstream source hashes.')


if __name__ == '__main__':
    main()
