"""Independent direct check of the source's explicit 24-word witness."""
from pathlib import Path
import hashlib
import json
import re
source = Path(__file__).resolve().parents[1] / 'source/Q7Mod/Canonical/LocalQ7W24Base.lean'
words = list(map(int, re.search(r'localQ7Code24Words[^\n]*:= \[([^]]+)\]', source.read_text()).group(1).split(',')))
code = set(words)
signatures = {v: {c for c in code if (v ^ c).bit_count() <= 1} for v in range(128)}
edges = [(u, v) for u in range(128) for v in range(u + 1, 128) if (u ^ v).bit_count() == 1]
result = {'witness': words, 'list_length': len(words), 'distinct_cardinality': len(code),
          'vertex_count': 128, 'undirected_edges': len(edges), 'directed_edges': 2 * len(edges),
          'edges_by_selected_endpoint_count': {str(k): sum((u in code) + (v in code) == k for u, v in edges) for k in range(3)},
          'undominated_vertices': [v for v in signatures if not signatures[v]],
          'unseparated_edges': [(u, v) for u, v in edges if signatures[u] == signatures[v]],
          'signature_0': sorted(signatures[0]), 'signature_1': sorted(signatures[1]),
          'witness_source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
if len(words) != 24 or len(code) != 24 or not all(0 <= c < 128 for c in code) or result['undominated_vertices'] or result['unseparated_edges']:
    raise RuntimeError('Witness failed: ' + json.dumps(result))
print(json.dumps(result, indent=2))
