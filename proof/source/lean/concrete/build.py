#!/usr/bin/env python3
"""Strict serial Lean build with source-closure fingerprints, resumability, and resource caps."""
import argparse,fcntl,hashlib,json,os,resource,signal,subprocess,sys,time
from pathlib import Path
from functools import lru_cache
root=Path(__file__).resolve().parent;os.chdir(root)
parser=argparse.ArgumentParser();parser.add_argument('targets',nargs='*');parser.add_argument('--accept-source-update',action='store_true');parser.add_argument('--clean',action='store_true');args=parser.parse_args()
lean=os.environ.get('LEAN',str(root.parent/'lean-4.19.0-linux/bin/lean'))
version=subprocess.check_output([lean,'--version'],text=True).strip()
if 'version 4.19.0,'not in version:raise SystemExit('Expected Lean4.19.0; found '+version)
os.environ['LEAN_PATH']='.'
logs=root/'logs';logs.mkdir(exist_ok=True)
(logs/'toolchain.txt').write_text(version+'\n')
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
files=sorted(root.rglob('*.lean'));snapshot={str(p.relative_to(root)):digest(p)for p in files}
manifest=root/'SOURCE-MANIFEST.json'
if manifest.exists()and json.loads(manifest.read_text())!=snapshot and not args.accept_source_update:
 raise SystemExit('Source manifest changed. Review changes, then explicitly pass --accept-source-update; recursive fingerprints will rebuild affected descendants.')
manifest.write_text(json.dumps(snapshot,indent=2,sort_keys=True)+'\n')
(root/'SOURCE-SHA256SUMS').write_text(''.join(h+'  '+p+'\n'for p,h in sorted(snapshot.items())))
cachefile=logs/'checked-modules.json';cache={}if args.clean or not cachefile.exists()else json.loads(cachefile.read_text())
def source(name):return root/(name.replace('.','/')+'.lean')
@lru_cache(None)
def imports(name):
 result=[]
 for line in source(name).read_text().splitlines():
  if line.startswith('import '):result +=[x for x in line.split()[1:]if x!='Std']
 return result
@lru_cache(None)
def fingerprint(name):
 record={'source':snapshot[str(source(name).relative_to(root))],'imports':{d:fingerprint(d)for d in imports(name)},'toolchain':version}
 return hashlib.sha256(json.dumps(record,sort_keys=True).encode()).hexdigest()
def verify_manifest():
 current={str(p.relative_to(root)):digest(p)for p in root.rglob('*.lean')}
 if current!=snapshot:raise SystemExit('Sources changed while the build was running; stopping before further compilation.')
def cap():resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
def stop(signum,frame):raise KeyboardInterrupt
signal.signal(signal.SIGTERM,stop)
visited=set()
def check(name):
 if name in visited:return
 for dep in imports(name):check(dep)
 src=source(name);out=src.with_suffix('.olean');fp=fingerprint(name);old=cache.get(name,{})
 if old.get('recursive_source_fingerprint')==fp and out.exists()and old.get('olean_sha256')==digest(out):
  visited.add(name);return
 # Inspect current source before every invocation; all sources are checked again at each root target.
 if digest(src)!=snapshot[str(src.relative_to(root))]:raise SystemExit('Source changed: '+name)
 print('CHECK '+name,flush=True)
 logfile=logs/(name.replace('.','_')+'.log');lockpath=Path(os.environ.get('LEAN_COMPILE_LOCK',str(root.parent/'.lean-compile.lock')))
 with open(lockpath,'a')as lock:
  fcntl.flock(lock,fcntl.LOCK_EX)
  start=time.monotonic();peak=0
  with open(logfile,'w')as log:
   proc=subprocess.Popen([lean,'-j','1','-o',str(out.relative_to(root)),str(src.relative_to(root))],stdout=log,stderr=subprocess.STDOUT,preexec_fn=cap,start_new_session=True)
   try:
    while proc.poll()is None:
     try:
      for line in Path(f'/proc/{proc.pid}/status').read_text().splitlines():
       if line.startswith('VmRSS:'):peak=max(peak,int(line.split()[1]))
     except FileNotFoundError:pass
     time.sleep(.1)
   except BaseException:
    try:os.killpg(proc.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    try:proc.wait(timeout=5)
    except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
    log.write(f'\nINTERRUPTED_CHILD_EXIT={proc.returncode}\nPEAK_RSS_KIB={peak}\n');raise
   elapsed=time.monotonic()-start
   log.write(f'\nEXIT_CODE={proc.returncode}\nELAPSED_SECONDS={elapsed:.4f}\nPEAK_RSS_KIB={peak}\nADDRESS_SPACE_LIMIT_BYTES={3*1024**3}\nLEAN_THREADS=1\nRECURSIVE_SOURCE_FINGERPRINT={fp}\n')
  fcntl.flock(lock,fcntl.LOCK_UN)
 if proc.returncode:
  print(logfile.read_text(),flush=True);raise SystemExit(proc.returncode)
 cache[name]={'recursive_source_fingerprint':fp,'olean_sha256':digest(out),'elapsed_seconds':elapsed,'peak_rss_kib':peak}
 cachefile.write_text(json.dumps(cache,indent=2,sort_keys=True)+'\n');visited.add(name)
 print(f'PASS {name} {elapsed:.2f}s {peak/1024:.1f}MiB',flush=True)
for target in args.targets or [f'Certificates.C{b:03}'for b in range(256)]+['Main']:
 verify_manifest();check(target)
 if target.startswith('Certificates.')or target=='Main':print('TARGET_COMPLETE '+target,flush=True)
verify_manifest()
print('REQUESTED_TARGETS_COMPLETE',flush=True)
if 'Main' in visited:print((logs/'Main.log').read_text(),flush=True)
