#!/usr/bin/env python3
"""Secondary exhaustive witness check; does not invoke or replace Lean."""
from collections import Counter
C = {0, 1, 2, 28, 29, 30, 43, 44, 51, 52, 59, 60,
     64, 71, 72, 79, 80, 87, 101, 102, 103, 121, 122, 123}
assert len(C) == 24 and all(0 <= c < 128 for c in C)
signatures = {v: {c for c in C if (v ^ c).bit_count() <= 1} for v in range(128)}
assert all(signatures.values())
edges = [(v, v ^ (1 << j)) for v in range(128) for j in range(7) if v < (v ^ (1 << j))]
assert len(edges) == 448
assert all(signatures[u] != signatures[v] for u, v in edges)
print('PASS: size 24; 128 domination checks; 448 adjacent-pair checks, all endpoint types')
print('Trace histogram:', dict(sorted(Counter(map(len, signatures.values())).items())))
print('Minimum separation size:', min(len(signatures[u] ^ signatures[v]) for u, v in edges))
print('Selected isolates:', sorted(c for c in C if all((c ^ (1 << j)) not in C for j in range(7))))

print('Edge endpoint classes:', dict(sorted(Counter(int(u in C) + int(v in C) for u, v in edges).items())))
