#!/usr/bin/env python3
"""Read-only source, import-order, and package-boundary preflight. No Lean invocation."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest = json.loads((ROOT / 'source-manifest.json').read_text())
    records = {r['module']: r for r in manifest['modules']}
    order = (ROOT / 'build-order.txt').read_text().splitlines()
    assert order == manifest['dependency_order']
    assert len(order) == len(set(order)) == 52
    assert set(order) == set(records)
    assert {p.name for p in (ROOT / 'Proofs').glob('*.lean')} == {
        n + '.lean' for n in records
    }, 'Unexpected or missing production/audit source'
    checked = 0
    for line in (ROOT / 'SOURCE_SHA256SUMS').read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = ROOT / relative
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, relative
        checked += 1
    seen = set()
    upstream = set((ROOT / 'direct-upstream-imports.txt').read_text().splitlines())
    for name in order:
        rec = records[name]
        source = ROOT / rec['path']
        assert hashlib.sha256(source.read_bytes()).hexdigest() == rec['source_sha256']
        text = source.read_text()
        # Deliberately conservative: these frozen sources contain no such tokens,
        # even in comments. The independent production audit is stronger evidence.
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|skipKernelTC', text), name
        imports = [word for line in text.splitlines()
                   if (match := re.match(r'^import\s+(.+?)(?:\s*--.*)?$', line))
                   for word in match[1].split()]
        assert imports == rec['imports'], name
        assert all(dep in seen or dep in upstream for dep in imports), name
        seen.add(name)
    print(f'PASS: {checked} source hashes; 51 production modules + 1 checked audit; dependency order closed.')


if __name__ == '__main__':
    main()
