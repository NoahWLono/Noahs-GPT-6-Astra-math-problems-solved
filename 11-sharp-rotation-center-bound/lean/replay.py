"""Fresh-output, bounded Lean replay. No package download or dependency rebuild."""
from pathlib import Path
import argparse, hashlib, json, os, signal, subprocess, time
p = argparse.ArgumentParser()
p.add_argument('--lean', required=True)
p.add_argument('--mathlib', required=True)
p.add_argument('--output', required=True)
a = p.parse_args()
root = Path(__file__).resolve().parent
out = Path(a.output).resolve()
out.mkdir(parents=True, exist_ok=False)
env = os.environ.copy()
env['PATH'] = str(Path(a.lean).resolve().parent) + ':' + env['PATH']
env['LEAN_NUM_THREADS'] = '1'
env['LEAN_PATH'] = str(out) + ':' + subprocess.check_output(
    ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=a.mathlib, env=env,
    text=True, timeout=15).strip()
modules = ['RotationComposition', 'ComplexWeightGeometry', 'RotationCoefficients', 'RotationCenterBound', 'RotationSharpness', 'RotationExpectedStatement', 'RotationAudit']
results = []
for name in modules:
    source = root / (name + '.lean')
    command = [a.lean, '-j1', '-M3072', '-R', str(root), '-o', str(out / (name + '.olean')), str(source)]
    start, peak, status = time.monotonic(), 0, 'finished'
    with (out / (name + '.log')).open('w') as log:
        proc = subprocess.Popen(command, cwd=a.mathlib, env=env, stdout=log,
            stderr=subprocess.STDOUT, start_new_session=True)
        while proc.poll() is None:
            rss = 0
            for item in Path('/proc').iterdir():
                if not item.name.isdigit(): continue
                try:
                    stat = (item / 'stat').read_text().split()
                    if int(stat[4]) == proc.pid:
                        rss += int(stat[23]) * os.sysconf('SC_PAGE_SIZE') // 1024
                except (OSError, ValueError, IndexError): pass
            peak = max(peak, rss)
            if rss > 3 * 1024 * 1024 or time.monotonic() - start > 30:
                status = 'rss_limit' if rss > 3 * 1024 * 1024 else 'timeout'
                os.killpg(proc.pid, signal.SIGKILL)
                break
            time.sleep(0.1)
        proc.wait()
    result = dict(module=name, exit_code=proc.returncode, status=status,
        source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        seconds=round(time.monotonic()-start,3), peak_group_rss_KiB=peak,
        time_limit_seconds=30, rss_limit_KiB=3*1024*1024)
    results.append(result)
    print(json.dumps(result), flush=True)
    (out / 'resources.json').write_text(json.dumps(results, indent=2))
    if proc.returncode:
        print((out / (name + '.log')).read_text())
        raise SystemExit(1)
print('All six theorem modules and the separate rotation-audit certificate passed. Inspect printed axiom lists in the logs.')
