#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
base=$(cd "$here/../../../lean-research" && pwd)
export PATH="$base/lean-4.19.0-linux/bin:$PATH"
cd "$base/mathlib4"
exec 9>"$base/.lean-compile.lock"
flock 9
export LEAN_PATH="$here:$(lake env printenv LEAN_PATH)"
export MALLOC_ARENA_MAX=2
ulimit -s 2048
name=${1:-UniformRow}
lean --root="$here" -j1 -s2048 -o "$here/$name.olean" "$here/$name.lean" &
pid=$!; peak=0; ticks=0
trap 'kill -TERM "$pid" 2>/dev/null || true' EXIT INT TERM
while kill -0 "$pid" 2>/dev/null; do
 ticks=$((ticks + 1)); if [[ $ticks -gt 1200 ]]; then echo '120s timeout'; kill -TERM "$pid"; fi
 rss=$(awk '/VmRSS/{print $2}' "/proc/$pid/status" 2>/dev/null || true)
 if [[ ${rss:-0} -gt $peak ]]; then peak=${rss:-0}; fi
 if [[ ${rss:-0} -gt 2900000 ]]; then echo 'RSS cap reached'; kill -TERM "$pid"; fi
 sleep 0.1
done
wait "$pid"
echo "PEAK_RSS_KIB=$peak"
trap - EXIT INT TERM
