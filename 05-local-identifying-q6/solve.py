import numpy as np, json,time
from scipy.optimize import milp,Bounds,LinearConstraint
from pathlib import Path
n=6; V=range(1<<n)
N=[{v}|{v^(1<<i) for i in range(n)} for v in V]
E=[(u,u^(1<<i)) for u in V for i in range(n) if u<u^(1<<i)]
S=N+[N[u]^N[v] for u,v in E]
A=np.array([[int(v in s) for v in V] for s in S],float)
l=np.zeros(64);l[0]=1
start=time.time()
r=milp(np.ones(64),integrality=np.ones(64),bounds=Bounds(l,np.ones(64)),constraints=LinearConstraint(A,1,np.inf),options={'time_limit':600,'disp':True,'mip_rel_gap':0})
print(r,flush=True)
if r.x is not None:
 C=[v for v in V if r.x[v]>.5];print('CODE',C,flush=True)
 assert all(set(C)&s for s in S)
 Path(__file__).with_name('result.json').write_text(json.dumps({'code':C,'size':len(C),'status':int(r.status),'message':r.message,'dual_bound':float(r.mip_dual_bound),'seconds':time.time()-start},indent=2))
