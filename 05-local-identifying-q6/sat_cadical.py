import sys,time,json
sys.path.insert(0,'/tmp/q6-sat')
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pathlib import Path
p=Path(__file__).parent
N=[{v}|{v^(1<<i) for i in range(6)} for v in range(64)]
E=[(u,u^(1<<i)) for u in range(64) for i in range(6) if u<u^(1<<i)]
clauses=[[v+1 for v in sorted(s)] for s in N+[N[u]^N[v] for u,v in E]]
clauses += [[1]]
card=CardEnc.atmost(lits=list(range(1,65)),bound=13,encoding=EncType.seqcounter)
clauses+=card.clauses
(p/'exclude13.cnf').write_text('p cnf %d %d\n'%(card.nv,len(clauses))+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
t=time.time()
with Solver(name='cadical195',bootstrap_with=clauses,with_proof=True) as s:
 result=s.solve();print('SAT?',result,'time',time.time()-t,'stats',s.accum_stats(),flush=True)
 if not result:
  proof=s.get_proof();(p/'exclude13-cadical.drat').write_text('\n'.join(proof)+'\n');print('proof',len(proof),flush=True)
 (p/'sat_cadical_result.json').write_text(json.dumps({'sat':result,'seconds':time.time()-t,'stats':s.accum_stats()},indent=2))
