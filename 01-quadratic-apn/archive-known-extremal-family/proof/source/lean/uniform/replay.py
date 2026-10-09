#!/usr/bin/env python3
"""Recheck frozen local sources, using installed Lean and inherited library paths."""
import argparse, hashlib, json, os, pathlib, subprocess, sys, time

p=argparse.ArgumentParser()
p.add_argument('--clean',action='store_true',help='Remove only generated local .olean/.ilean files before replay')
p.add_argument('--lean',default='lean',help='Lean executable (default: lean on PATH)')
p.add_argument('--lock',help='Optional shared advisory compile-lock file, for Unix audit hosts')
a=p.parse_args()
root=pathlib.Path(__file__).resolve().parent
manifest=json.loads((root/'SOURCE_MANIFEST.json').read_text())
order=(root/'REPLAY_ORDER.txt').read_text().splitlines()
assert order==[x['module'] for x in manifest]
for item in manifest:
    src=root.joinpath(*item['module'].split('.')).with_suffix('.lean')
    if hashlib.sha256(src.read_bytes()).hexdigest()!=item['sha256']:
        sys.exit('SOURCE HASH MISMATCH: '+str(src))
    if a.clean:
        for ext in ['.olean','.ilean']:
            src.with_suffix(ext).unlink(missing_ok=True)
env=os.environ.copy()
inherited=[str(pathlib.Path(x).resolve()) for x in env.get('LEAN_PATH','').split(os.pathsep) if x]
env['LEAN_PATH']=os.pathsep.join([str(root)]+inherited)
env['MALLOC_ARENA_MAX']='2'
if os.name=='posix':
    import resource
    soft,hard=resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK,(min(2097152,hard) if hard>=0 else 2097152,hard))
(root/'EFFECTIVE_LEAN_PATH.txt').write_text(env['LEAN_PATH']+'\n')
lock=open(a.lock,'w') if a.lock else None
if lock:
    import fcntl
    fcntl.flock(lock,fcntl.LOCK_EX)
try:
    subprocess.run([a.lean,'--version'],check=True,env=env)
    for mod in order:
        src=root.joinpath(*mod.split('.')).with_suffix('.lean')
        print(f'BEGIN {mod} {time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime())}',flush=True)
        proc=subprocess.Popen([a.lean,'--root='+str(root),'-j1','-s2048','-o',str(src.with_suffix('.olean')),str(src)],env=env)
        peak=0
        while proc.poll() is None:
            try:
                status=pathlib.Path(f'/proc/{proc.pid}/status').read_text()
                rss=int(next(l for l in status.splitlines() if l.startswith('VmRSS:')).split()[1])
                peak=max(peak,rss)
                if rss>3145728:
                    print('MEMORY CAP EXCEEDED',flush=True);proc.terminate()
            except (FileNotFoundError,ProcessLookupError,StopIteration):pass
            time.sleep(.05)
        print(f'END {mod} status={proc.returncode} peak_KiB={peak}',flush=True)
        if proc.returncode:sys.exit(proc.returncode)
    print('SOURCE_ONLY_REPLAY_PASS',flush=True)
finally:
    if lock:lock.close()
