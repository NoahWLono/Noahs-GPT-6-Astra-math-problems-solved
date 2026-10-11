"""Check graph clauses and explicit satisfying extension of every <=13 assignment."""
from pathlib import Path
import json
P=Path(__file__).parent
lines=(P/'exclude13.cnf').read_text().splitlines(); assert lines[0]=='p cnf 727 1621'
cs=[tuple(map(int,l.split()[:-1])) for l in lines[1:]]
assert len(cs)==1621
balls=[{w for w in range(64) if (w^v).bit_count()<=1} for v in range(64)]
edges=[(u,v) for u in range(64) for v in range(u+1,64) if (u^v).bit_count()==1]
expected=[tuple(sorted(w+1 for w in b)) for b in balls]+[tuple(sorted(w+1 for w in balls[u]^balls[v])) for u,v in edges]+[(1,)]
assert cs[:257]==expected
counter=cs[257:]; mapping={}
def put(v,ij):
    assert 65<=v<=727
    if v in mapping: assert mapping[v]==ij
    else: mapping[v]=ij
for _ in range(728):
    old=len(mapping)
    for c in counter:
        if len(c)==2 and -64<=c[0]<=-1 and c[1]>64: put(c[1],(-c[0],1))
        elif len(c)==2 and c[0]<-64 and c[1]>64 and -c[0] in mapping:
            i,j=mapping[-c[0]]; put(c[1],(i+1,j))
        elif len(c)==3 and -64<=c[0]<=-1 and c[1]<-64 and c[2]>64 and -c[1] in mapping:
            i,j=mapping[-c[1]]; assert -c[0]==i+1; put(c[2],(i+1,j+1))
    if len(mapping)==old: break
assert len(mapping)==663 and len(set(mapping.values()))==663
assert set(mapping.values())=={(i,j) for j in range(1,14) for i in range(j,j+51)}
types={k:0 for k in ['input','monotonicity','increment','overflow']}
for c in counter:
    if len(c)==2 and -64<=c[0]<=-1 and c[1]>64:
        assert mapping[c[1]]==(-c[0],1); types['input']+=1
    elif len(c)==2 and c[0]<-64 and c[1]>64:
        i,j=mapping[-c[0]]; assert mapping[c[1]]==(i+1,j); types['monotonicity']+=1
    elif len(c)==3:
        assert -64<=c[0]<=-1 and c[1]<-64 and c[2]>64
        i,j=mapping[-c[1]]; assert -c[0]==i+1 and mapping[c[2]]==(i+1,j+1); types['increment']+=1
    else:
        assert len(c)==2 and -64<=c[0]<=-1 and c[1]<-64
        i,j=mapping[-c[1]]; assert -c[0]==i+1 and j==13; types['overflow']+=1
print(json.dumps(dict(result='PASS',graph_clauses=257,counter_clauses=len(counter),auxiliary_variables=len(mapping),clause_types=types,extension='s(i,j) = 1 iff sum(x_1,...,x_i) >= j; each actual counter clause is satisfied whenever sum(x_1,...,x_64)<=13'),indent=2))
