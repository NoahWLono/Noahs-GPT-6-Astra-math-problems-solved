"""Independent stdlib RUP-only LRAT checker. No SAT library or solver imported."""
import sys, hashlib, json, time
from pathlib import Path

def check(cnf, proof):
    start=time.time(); clauses={}; pending=[]; nv=nc=None
    for line in open(cnf):
        if line.startswith('c') or not line.strip(): continue
        if line.startswith('p'):
            _,typ,nv,nc=line.split(); assert typ=='cnf'; nv=int(nv); nc=int(nc); continue
        for lit in map(int,line.split()):
            if lit: assert abs(lit)<=nv; pending.append(lit)
            else: clauses[len(clauses)+1]=tuple(pending); pending=[]
    assert not pending and len(clauses)==nc
    highest=nc; stamp=[0]*(nv+1); val=[0]*(nv+1); epoch=0; additions=hints=deletions=0; empty=False
    for line_no,line in enumerate(open(proof),1):
        words=line.split()
        if not words or words[0]=='c': continue
        ident=int(words[0])
        if words[1]=='d':
            ids=list(map(int,words[2:])); assert ids[-1]==0 and 0 not in ids[:-1]
            for cid in ids[:-1]:
                assert cid in clauses, ('unknown deletion',line_no,cid)
                del clauses[cid]; deletions+=1
            continue
        a=list(map(int,words[1:])); z=a.index(0); clause=tuple(a[:z]); refs=a[z+1:]
        assert ident>highest and refs and refs[-1]==0 and all(r>0 for r in refs[:-1])
        assert all(0<abs(l)<=nv for l in clause)
        highest=ident; epoch+=1; conflict=False
        for lit in clause:
            v=abs(lit); wanted=-1 if lit>0 else 1
            if stamp[v]==epoch and val[v]!=wanted: conflict=True
            stamp[v]=epoch; val[v]=wanted
        for cid in refs[:-1]:
            assert cid in clauses, ('unknown hint',line_no,cid)
            hints+=1
            if conflict: continue
            unit=0; multiple=False; satisfied=False
            for lit in clauses[cid]:
                v=abs(lit)
                if stamp[v]!=epoch:
                    if unit and unit!=lit: multiple=True
                    unit=lit
                elif val[v]==(1 if lit>0 else -1): satisfied=True; break
            assert not satisfied and not multiple, ('non-unit hint',line_no,cid)
            if not unit: conflict=True
            else:
                v=abs(unit); stamp[v]=epoch; val[v]=1 if unit>0 else -1
        assert conflict, ('no conflict',line_no)
        clauses[ident]=clause; additions+=1
        if not clause: empty=True
    assert empty, 'No empty clause derived'
    return dict(result='VERIFIED UNSAT by independent RUP checker',variables=nv,input_clauses=nc,additions=additions,hints=hints,deletions=deletions,seconds=time.time()-start,cnf_sha256=hashlib.sha256(Path(cnf).read_bytes()).hexdigest(),proof_sha256=hashlib.sha256(Path(proof).read_bytes()).hexdigest())
if __name__=='__main__': print(json.dumps(check(*sys.argv[1:]),indent=2))
