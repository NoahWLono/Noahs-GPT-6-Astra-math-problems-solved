"""Snapshot the exact final proof dependency closure, then kernel-check it afresh.
No previously generated project .olean files are copied or placed on LEAN_PATH.
The official toolchain's builtin Lean/Std .oleans remain part of the toolchain.
"""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys, time
BASE=Path(__file__).resolve().parent
SRC=BASE/'lean'
LEAN=os.environ.get('LEAN','/tmp/lean-4.24.0-linux/bin/lean')
DEST=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else BASE/'lean-clean-check'
if DEST.exists():
    raise SystemExit(f'Refusing to overwrite existing independent check directory: {DEST}')
order=[]; seen=set(); resources=set()
def visit(module):
    if module in seen:return
    path=SRC/(module.replace('.','/')+'.lean')
    if not path.exists():return  # builtin Lean/Std imports
    seen.add(module)
    text=path.read_text()
    for line in text.splitlines():
        m=re.match(r'^import\s+(\S+)\s*$',line)
        if m:visit(m.group(1))
    for resource in re.findall(r'^replay_rup%[ \t]+"([^"\r\n]+)"[ \t]*$',text,re.M):resources.add(resource)
    order.append(module)
visit('FullTheorem')
if not order or order[-1]!='FullTheorem':raise SystemExit('Final theorem dependency closure missing')
DEST.mkdir(parents=True)
paths=[m.replace('.','/')+'.lean' for m in order]+sorted(resources)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest={}
for rel in paths:
    source=SRC/rel; target=DEST/rel; target.parent.mkdir(parents=True,exist_ok=True)
    before=sha(source); shutil.copyfile(source,target)
    if sha(target)!=before:raise SystemExit(f'Snapshot mismatch: {rel}')
    manifest[rel]=before
(DEST/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(DEST/'build-order.json').write_text(json.dumps(order,indent=2)+'\n')
record={'toolchain':subprocess.check_output([LEAN,'--version'],text=True).strip(),
        'source_files':len(manifest),'modules':len(order),'completed':0,'success':False,
        'source_manifest_sha256':sha(DEST/'source-manifest.json')}
(DEST/'status.json').write_text(json.dumps(record,indent=2)+'\n')
env=dict(os.environ,LEAN_PATH=str(DEST));start=time.time();results=[]
with (DEST/'check.log').open('w') as log:
    for i,module in enumerate(order):
        rel=module.replace('.','/');t=time.time()
        print(f'[{i+1}/{len(order)}] {module}',flush=True)
        log.write(f'\nCHECKING {module}\n');log.flush()
        process=subprocess.Popen([LEAN,'-j1','-DElab.async=false','-Dlinter.unusedVariables=false',
            '-o',rel+'.olean',rel+'.lean'],cwd=DEST,env=env,stdout=log,stderr=log)
        _,status,usage=os.wait4(process.pid,0);code=os.waitstatus_to_exitcode(status)
        process.returncode=code
        step={'module':module,'returncode':code,'seconds':time.time()-t,
              'peak_rss_kb':usage.ru_maxrss}
        if code==0:step['olean_sha256']=sha(DEST/(rel+'.olean'))
        results.append(step)
        record.update(completed=i+1,current=module,returncode=code,seconds=time.time()-start)
        (DEST/'status.json').write_text(json.dumps(record,indent=2)+'\n')
        (DEST/'build-results.json').write_text(json.dumps(results,indent=2)+'\n')
        if code:raise SystemExit(code)
record.update(success=True,seconds=time.time()-start)
(DEST/'status.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
