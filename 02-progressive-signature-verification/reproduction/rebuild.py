import os, pathlib, subprocess, time, json, fcntl, resource
root=pathlib.Path(__file__).resolve().parent
base=pathlib.Path(os.environ['LEAN_RESEARCH']).resolve(); src=root/'source'; logs=root/'logs'; logs.mkdir(exist_ok=True)
env=dict(os.environ, PATH=str(base/'lean-4.19.0-linux/bin')+':'+os.environ['PATH'], MALLOC_ARENA_MAX='2')
p=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=base/'mathlib4',env=env,text=True).strip()
env['LEAN_PATH']=str(src)+':'+p
(root/'environment.json').write_text(json.dumps({'LEAN_PATH':env['LEAN_PATH'],'lean':subprocess.check_output(['lean','--version'],env=env,text=True).strip(),'mathlib_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=base/'mathlib4',text=True).strip(),'rss_cap_kib':2900000,'module_timeout_seconds':120},indent=2))
mods=(src/'modules-v2.txt').read_text().split() if not os.environ.get('AUDIT_ONLY') else []; results=[]; start=time.monotonic()
def limits(): resource.setrlimit(resource.RLIMIT_STACK,(2048*1024,2048*1024))
for mod in mods+(['AuditAxioms'] if (src/'AuditAxioms.lean').exists() else []):
 with open(base/'.lean-compile.lock','w') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX); t=time.monotonic(); peak=0; reason=None
  with open(logs/(mod+'.log'),'w') as out:
   cmd=['lean','--root='+str(src),'-j1','-s2048','-o',str(src/(mod+'.olean')),str(src/(mod+'.lean'))]
   proc=subprocess.Popen(cmd,cwd=base/'mathlib4',env=env,stdout=out,stderr=subprocess.STDOUT,preexec_fn=limits)
   while proc.poll() is None:
    try:
     rss=next((int(x.split()[1]) for x in pathlib.Path('/proc/'+str(proc.pid)+'/status').read_text().splitlines() if x.startswith('VmRSS:')),0);peak=max(peak,rss)
    except (FileNotFoundError,ProcessLookupError): pass
    if peak>2900000 or time.monotonic()-t>120:
     reason='RSS cap' if peak>2900000 else 'timeout';proc.terminate()
     try:proc.wait(timeout=3)
     except subprocess.TimeoutExpired:proc.kill()
    time.sleep(.05)
   rc=proc.wait(); elapsed=time.monotonic()-t
   out.write(f'\nEXIT_CODE={rc}\nELAPSED_SECONDS={elapsed:.3f}\nPEAK_RSS_KIB={peak}\nLIMIT_REASON={reason}\n')
  row={'module':mod,'exit_code':rc,'elapsed_seconds':elapsed,'peak_rss_kib':peak,'limit_reason':reason};results.append(row)
  (root/'results.json').write_text(json.dumps({'total_wall_seconds':time.monotonic()-start,'modules':results},indent=2));print(json.dumps(row),flush=True)
  if rc:raise SystemExit(rc)
