#!/usr/bin/env python3
"""Reassemble transport parts and verify each source byte before atomic extraction."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parent

def check(ok, message):
    if not ok:
        raise RuntimeError(message)

def ensure_sources(root=ROOT):
    root = Path(root).resolve()
    target = root / 'source'
    check(not target.is_symlink(), 'Refusing symlink source root')
    if target.exists():
        return  # The main verifier checks complete exact contents, never merges.
    manifest = json.loads((root / 'transport/PARTS.json').read_text())
    check(manifest['format'] == 'concatenated-gzip-tar-v1', 'Unknown transport format')
    entries = []
    for filename, key in [('SOURCE_MANIFEST.json', 'modules'), ('JSON_MANIFEST.json', 'files')]:
        entries.extend(json.loads((root / 'manifests' / filename).read_text())[key])
    expected = {'source/' + entry['path']: entry for entry in entries}
    check(len(expected) == 4490, 'Unexpected source/data coverage')
    for name in expected:
        check(not Path(name).is_absolute() and '..' not in Path(name).parts, 'Unsafe manifest path')
    staging = Path(tempfile.mkdtemp(prefix='.source-unpack-', dir=root))
    try:
        archive = staging / 'source.tar.gz'
        combined = hashlib.sha256()
        total = 0
        with archive.open('wb') as stream:
            for index, part in enumerate(manifest['parts']):
                check(part['path'] == f'transport/source.tar.gz.part{index:03d}', 'Unexpected part path/order')
                path = root / part['path']
                check(path.is_file() and not path.is_symlink(), 'Missing regular archive part')
                data = path.read_bytes()
                check(len(data) == part['bytes'] and hashlib.sha256(data).hexdigest() == part['sha256'],
                      'Archive part hash mismatch: ' + part['path'])
                stream.write(data)
                combined.update(data)
                total += len(data)
        check(total == manifest['archive_bytes'] and combined.hexdigest() == manifest['archive_sha256'],
              'Combined archive hash mismatch')
        seen = set()
        with tarfile.open(archive, 'r:gz') as tar:
            for member in tar:
                name = member.name.rstrip('/')
                check(not Path(name).is_absolute() and '..' not in Path(name).parts, 'Unsafe tar path')
                if member.isdir():
                    check(name == 'source' or any(p.startswith(name + '/') for p in expected), 'Unexpected tar directory')
                    continue
                check(member.isfile() and name in expected and name not in seen,
                      'Unexpected, duplicate, or nonregular tar member: ' + name)
                entry = expected[name]
                check(member.size == entry['bytes'], 'Wrong source size: ' + name)
                reader = tar.extractfile(member)
                check(reader is not None, 'Unreadable tar member')
                data = reader.read()
                check(hashlib.sha256(data).hexdigest() == entry['sha256'], 'Source hash mismatch: ' + name)
                output = staging / name
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_bytes(data)
                seen.add(name)
        check(seen == set(expected), 'Archive omits proof inputs')
        check(not target.exists(), 'Source directory appeared during extraction')
        os.rename(staging / 'source', target)
    finally:
        shutil.rmtree(staging)

if __name__ == '__main__':
    ensure_sources()
    print('Source tree is present. Run verify.py --check-inputs for full integrity checks.')
