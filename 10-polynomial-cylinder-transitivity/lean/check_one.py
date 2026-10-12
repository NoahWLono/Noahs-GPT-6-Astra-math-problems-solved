#!/usr/bin/env python3
"""Bounded, single-thread Lean check with reproducible resource/status evidence."""
import hashlib,json,os,resource,subprocess,sys,time
from pathlib import Path
root=Path(__file__).resolve().parent.parent
module=sys.argv[1]
limit=int(sys.argv[2]) if len(sys.argv)>2 else 30
mathlib=Path(os.environ['MATHLIB_ROOT']).resolve()
env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
(root/'build').mkdir(exist_ok=True)
log=root/'build'/f'{module}.log';obj=root/'build'/f'{module}.olean'
obj.unlink(missing_ok=True)
source_hash=hashlib.sha256((root/'lean'/f'{module}.lean').read_bytes()).hexdigest()
cmd=['timeout','--kill-after=5',str(limit),'lake','env','bash','-c',
 'export LEAN_PATH="$1/build:$LEAN_PATH"; exec stdbuf -oL -eL lean -j1 -M3072 -R "$1/lean" -o "$1/build/$2.olean" "$1/lean/$2.lean"',
 'bash',str(root),module]
t=time.monotonic()
with log.open('w') as out: result=subprocess.run(cmd,cwd=mathlib,env=env,stdout=out,stderr=subprocess.STDOUT)
stats={'module':module,'exit_code':result.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'max_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'timeout_seconds':limit,'memory_limit_mib':3072,'threads':1,'object_exists':obj.exists(),'source_sha256':source_hash,'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if obj.exists() else None}
(root/'build'/f'{module}.run.json').write_text(json.dumps(stats,indent=2)+'\n')
print(log.read_text());print(json.dumps(stats));sys.exit(result.returncode)
