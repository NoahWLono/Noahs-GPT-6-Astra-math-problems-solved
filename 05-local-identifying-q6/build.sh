#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ "$#" -ne 1 ]; then
  echo "Usage: LEAN=/path/to/lean ./build.sh /absolute/new-check-directory" >&2
  exit 2
fi
python3 materialize_certificates.py
prefix="$("${LEAN:-lean}" --print-prefix)"
export LEAN="$prefix/bin/lean"
"$LEAN" --version | grep 'version 4.24.0,' >/dev/null || { echo 'Lean 4.24.0 is required.' >&2; exit 2; }
exec python3 verify_lean_clean.py "$1"
