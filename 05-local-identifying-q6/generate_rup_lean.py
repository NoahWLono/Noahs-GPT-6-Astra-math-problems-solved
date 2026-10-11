from pathlib import Path
import argparse,json
ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=200);ap.add_argument('--chunk',type=int,default=100);ap.add_argument('--path',action='store_true');args=ap.parse_args()
p=Path(__file__).parent; module='RUPPath' if args.path else 'RUP'; ns='Q6'+module; source='exclude13-path' if args.path else 'exclude13'; ninput=1623 if args.path else 1621; d=p/'lean'/module;d.mkdir(exist_ok=True)
clauses={}
for l in (p/(source+'.cnf')).read_text().splitlines():
 if l.startswith('p'):continue
 clauses[len(clauses)+1]=list(map(int,l.split()[:-1]))
def lit(l):return f'p {l}' if l>0 else f'¬ p {-l}'
def prop(c):return ' ∨ '.join('('+lit(l)+')' for l in c) if c else 'False'
with (d/'Inputs.lean').open('w') as f:
 f.write('import Lean\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\n')
 values=list(clauses.items())
 for offset in range(0,len(values),50):
  f.write(f'structure InputChunk{offset//50} (p : Nat → Prop) : Prop where\n')
  for i,c in values[offset:offset+50]: f.write(f'  c{i} : {prop(c)}\n')
 f.write('structure Inputs (p : Nat → Prop) : Prop where\n')
 for j in range((len(values)+49)//50): f.write(f'  chunk{j} : InputChunk{j} p\n')
 f.write('end '+ns+'\n')

def inject(j,n):
 t='t'
 if j<n-1:t=f'Or.inl ({t})'
 for k in range(j):t=f'Or.inr ({t})'
 return t
f=None;count=0; files=[]
for line in (p/(source+'.lrat')).open():
 a=line.split()
 if a[1]=='d':
  for k in a[2:-1]: clauses.pop(int(k),None)
  continue
 nums=list(map(int,a));i=nums[0];z=nums.index(0);c=nums[1:z];hints=nums[z+1:-1]
 if count%args.chunk==0:
  if f:f.write('end '+ns+'\n');f.close()
  idx=count//args.chunk;name=f'Chunk{idx:04d}';files.append(name)
  f=(d/(name+'.lean')).open('w');prev='Inputs' if idx==0 else f'Chunk{idx-1:04d}'
  f.write(f'import {module}.{prev}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\n')
 f.write(f'theorem c{i} (p : Nat → Prop) (h : Inputs p) : {prop(c)} := by\n  classical\n  exact Classical.byContradiction (fun n =>\n')
 known={};kidx=0
 for j,l in enumerate(c):
  name=f'k{kidx}';kidx+=1
  exp=f'fun t => n ({inject(j,len(c))})'
  if l<0:exp=f'Classical.byContradiction ({exp})'
  f.write(f'    let {name} : {lit(-l)} := {exp}\n');known[-l]=name
 conflict=False
 for hid in hints:
  hc=clauses[hid]
  todo=[l for l in hc if -l not in known]
  if any(l in known for l in hc):raise Exception('satisfied hint')
  if len(todo)>1:raise Exception(('nonunit',hid,todo))
  target=todo[0] if todo else None
  typ=lit(target) if target else 'False'
  def eliminate(j):
   l=hc[j]
   if target==l:body='t'
   else:
    clash=f'{known[-l]} t' if l>0 else f't {known[-l]}'
    body=f'False.elim ({clash})' if target else f'({clash})'
   func=f'(fun t => {body})'
   if j==len(hc)-1:return func
   return f'(fun t => Or.elim t {func} {eliminate(j+1)})'
  hp=f'h.chunk{(hid-1)//50}.c{hid}' if hid<=ninput else f'c{hid} p h'
  expression=f'{eliminate(0)} ({hp})' if hc else hp
  if target:
   name=f'k{kidx}';kidx+=1;known[target]=name
   f.write(f'    let {name} : {typ} := {expression}\n')
  else:
   f.write(f'    {expression})\n');conflict=True;break
 if not conflict:raise Exception('no conflict')
 clauses[i]=c;count+=1
 if count>=args.limit:break
if f:f.write('end '+ns+'\n');f.close()
print(json.dumps({'lemmas':count,'modules':len(files),'last':i}))
