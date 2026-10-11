"""Compare path instance to independently audited original instance."""
from pathlib import Path
p=Path(__file__).parent
exec((p/'independent_encoding_check.py').read_text())
def clauses(name):
 return [tuple(map(int,l.split()[:-1])) for l in (p/name).read_text().splitlines()[1:]]
a=clauses('exclude13.cnf');b=clauses('exclude13-path.cnf')
assert sorted(a[:256])==sorted(b[:256])
assert b[256:259]==[(1,),(2,),(3,)]
assert a[257:]==b[259:]
print('PASS: path instance changes only normalization from {0} to {0,1,2}')
