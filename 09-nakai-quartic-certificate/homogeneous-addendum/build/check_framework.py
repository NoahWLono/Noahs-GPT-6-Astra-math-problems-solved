"""One bounded, single-threaded local Lean check."""
from pathlib import Path
import hashlib
import json
import os
import signal
import subprocess
import sys
import time

root = Path(__file__).resolve().parent.parent
mathlib = Path(os.environ['MATHLIB_ROOT'])
build = Path(os.environ['NAKAI_BUILD_DIR'])
build.mkdir(parents=True, exist_ok=True)
lean_binary = os.environ['LEAN_BINARY']
module = sys.argv[1] if len(sys.argv) > 1 else 'NakaiFramework'
tag = sys.argv[2] if len(sys.argv) > 2 else 'checked'
source = root / 'lean' / (module + '.lean')
if not source.is_file() or '/' in module or '/' in tag:
    raise SystemExit('Expected one existing project module and a simple log tag.')
env = os.environ.copy()
env['PATH'] = str(Path(lean_binary).parent) + ':' + env['PATH']
env['LEAN_NUM_THREADS'] = '1'
lake_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                    env=env, cwd=mathlib, text=True, timeout=15).strip()
env['LEAN_PATH'] = str(build) + (':' + lake_path if lake_path else '')
# Let Lake exit before checking: its resident runtime need not coexist with Lean.
command = [lean_binary,
           '-j1', '-M3072', '-R', str(root / 'lean'),
           '-o', str(build / (module + '.olean')), str(source)]
digest = hashlib.sha256(source.read_bytes()).hexdigest()
# Final-import checks use a larger fixed RSS guard.
rss_limit_kib = int((3.75 if module in ('NakaiConcrete', 'NakaiExpected') else 3) * 1024 * 1024)
time_limit_seconds = 60 if module in ('NakaiConcrete', 'NakaiExpected') else 30
start = time.monotonic()
peak = 0
status = 'finished'
log_path = build / (module + '.' + tag + '.log')
with log_path.open('w') as log:
    process = subprocess.Popen(command, env=env, cwd=mathlib, stdout=log,
                               stderr=subprocess.STDOUT, start_new_session=True)
    while process.poll() is None:
        rss = 0
        for entry in Path('/proc').iterdir():
            if not entry.name.isdigit():
                continue
            try:
                fields = (entry / 'stat').read_text().split()
                if int(fields[4]) == process.pid:
                    rss += int(fields[23]) * os.sysconf('SC_PAGE_SIZE') // 1024
            except (OSError, ValueError, IndexError):
                pass
        peak = max(peak, rss)
        if rss > rss_limit_kib or time.monotonic() - start > time_limit_seconds:
            status = 'rss_limit' if rss > rss_limit_kib else 'timeout'
            os.killpg(process.pid, signal.SIGKILL)
            break
        time.sleep(0.1)
    process.wait()
result = dict(command=command, source_sha256=digest, exit_code=process.returncode,
              status=status, seconds=round(time.monotonic() - start, 3),
              peak_group_rss_KiB=peak, rss_limit_KiB=rss_limit_kib,
              time_limit_seconds=time_limit_seconds)
(build / (module + '.' + tag + '.resources.json')).write_text(json.dumps(result, indent=2))
print(json.dumps(result))
print(log_path.read_text())
raise SystemExit(process.returncode if process.returncode >= 0 else 1)
