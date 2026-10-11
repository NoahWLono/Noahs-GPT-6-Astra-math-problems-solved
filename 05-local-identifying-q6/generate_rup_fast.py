from pathlib import Path
import json,argparse
ap=argparse.ArgumentParser();ap.add_argument("--prefix-count",type=int,default=0);ap.add_argument("--batch-size",type=int,default=500);args=ap.parse_args()
p=Path(__file__).parent;d=p/'lean/RUPPathFast';d.mkdir(exist_ok=True)
cs={}
for l in (p/'exclude13-path.cnf').read_text().splitlines():
 if not l.startswith('p'):cs[len(cs)+1]=list(map(int,l.split()[:-1]))
steps=[];index=0
for line in (p/'exclude13-path.lrat').open():
 a=line.split()
 if a[1]=='d':
  for k in a[2:-1]:cs.pop(int(k),None)
  continue
 n=list(map(int,a));ident=n[0];z=n.index(0);cl=n[1:z];hints=n[z+1:-1]
 steps.append({'id':ident,'target':cl,'hints':[[h,cs[h]] for h in hints]});cs[ident]=cl
 if len(steps)==(100 if index<args.prefix_count else args.batch_size) or cl==[]:
  name=f'Chunk{index:04d}';(d/(name+'.json')).write_text(json.dumps(steps,separators=(',',':')))
  imports='import RUPReplay\n'+(f'import RUPPathFast.Chunk{index-1:04d}\n' if index else '')
  (d/(name+'.lean')).write_text(imports+'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'+f'replay_rup% "RUPPathFast/{name}.json"\n')
  steps=[];index+=1
for f in d.glob('Chunk*'):
 if f.suffix in ['.json','.lean','.olean'] and int(f.stem[5:])>=index: f.unlink()
print('Generated',index,'modules')
