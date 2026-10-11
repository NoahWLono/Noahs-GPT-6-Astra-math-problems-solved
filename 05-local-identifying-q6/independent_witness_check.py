"""Standard-library exact direct definition check for the 14-word Q6 code."""
from itertools import combinations
from collections import Counter
import json
from pathlib import Path
CODE=(0,4,15,23,26,29,31,33,35,36,41,49,58,62)

def main():
    assert len(CODE)==len(set(CODE))==14 and all(0<=c<64 for c in CODE)
    # Use Hamming distance, independently of the construction's flip-based balls.
    signature={v:tuple(c for c in CODE if (v^c).bit_count()<=1) for v in range(64)}
    assert all(signature.values())
    edges=[(u,v) for u,v in combinations(range(64),2) if (u^v).bit_count()==1]
    assert len(edges)==192 and all(signature[u]!=signature[v] for u,v in edges)
    witnesses=[{'edge':[u,v],'separating_codeword':min(set(signature[u])^set(signature[v]))} for u,v in edges]
    code_edges=[(u,v) for u,v in edges if u in CODE and v in CODE]
    degree={c:sum((c^d).bit_count()==1 for d in CODE) for c in CODE}
    assert all(not(degree[u]==degree[v]==1) for u,v in code_edges)
    for c in CODE:
        if degree[c]==0:assert all(len(signature[v])>=2 for v in range(64) if (v^c).bit_count()==1)
    return {'code':CODE,'binary_code':[format(c,'06b') for c in CODE],'size':14,'covered_vertices':64,'adjacent_pairs_checked':192,'code_code_edges_checked':len(code_edges),'edges_with_code_endpoint_checked':sum(u in CODE or v in CODE for u,v in edges),'signature_size_distribution':dict(Counter(map(len,signature.values()))),'induced_code_degrees':degree,'vertex_signatures':signature,'edge_separation_witnesses':witnesses,'conclusion':'Exact upper bound M_L(6)<=14 only; optimality not certified here.'}
if __name__=='__main__':
    result=main();print(json.dumps(result,indent=2))
