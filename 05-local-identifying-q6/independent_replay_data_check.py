"""Independent linkage: CNF -> Lean input propositions; LRAT -> JSON replay data."""
from pathlib import Path
import re,json,hashlib
p=Path(__file__).parent
cnf=[list(map(int,l.split()[:-1])) for l in (p/'exclude13-path.cnf').read_text().splitlines()[1:]]
source=(p/'lean/RUPPath/Inputs.lean').read_text()
rows=re.findall(r'^  c(\d+) : (.+)$',source,re.M)
assert len(rows)==len(cnf)==1623
for (ident,prop),c in zip(rows,cnf):
 assert int(ident)==rows.index((ident,prop))+1
 expected=' ∨ '.join(f'(p {l})' if l>0 else f'(¬ p {-l})' for l in c)
 assert prop==expected,(ident,prop,expected)
files=sorted((p/'lean/RUPPathFast').glob('Chunk*.json'))
def jsonsteps():
 for f in files:
  yield from json.loads(f.read_text())
steps=iter(jsonsteps());active={i+1:c for i,c in enumerate(cnf)};count=0;final=None
for line in (p/'exclude13-path.lrat').open():
 a=line.split()
 if a[1]=='d':
  for k in a[2:-1]: del active[int(k)]
  continue
 ns=list(map(int,a));z=ns.index(0);ident=ns[0];cl=ns[1:z];refs=ns[z+1:-1]
 s=next(steps)
 assert s=={'id':ident,'target':cl,'hints':[[h,active[h]] for h in refs]}
 active[ident]=cl;count+=1;final=s
assert next(steps,None) is None
assert final['id']==92061 and final['target']==[]
assert 'minimum_fourteen_of_path_refutation Q6RUPPath.c92061' in (p/'lean/FullTheorem.lean').read_text()
print(json.dumps(dict(result='PASS',input_propositions=1623,replay_modules=len(files),replay_steps=count,final_clause_id=92061,final_clause=[],engine_sha256=hashlib.sha256((p/'lean/RUPReplay.lean').read_bytes()).hexdigest()),indent=2))
