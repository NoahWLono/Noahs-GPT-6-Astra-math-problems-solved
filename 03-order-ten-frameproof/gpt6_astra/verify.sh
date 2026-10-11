#!/usr/bin/env bash
# Verify the distribution and replay the complete proof sequentially.
set -euo pipefail

task_root="$(cd -- "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd -- "$task_root"

if [[ $# -ne 0 ]]; then
  printf '%s\n' 'Usage: ./verify.sh' >&2
  printf '%s\n' 'Checks hashes and pins, builds sequentially, then freshly rechecks all five theorem modules.' >&2
  exit 2
fi

for task_required in SHA256SUMS MainTheorem.lean certificates/case2.lrat certificates/case3.lrat certificates/case4.lrat certificates/case5.lrat; do
  if [[ ! -f "$task_required" ]]; then
    printf 'Required release file is missing: %s\n' "$task_required" >&2
    exit 1
  fi
done

if command -v sha256sum >/dev/null 2>&1; then
  sha256sum -c SHA256SUMS
elif command -v shasum >/dev/null 2>&1; then
  shasum -a 256 -c SHA256SUMS
else
  printf '%s\n' 'Install sha256sum or shasum to check the release manifest.' >&2
  exit 1
fi

task_expected_lean='5045d0056413266e57c625dcd7c365b10e377c52'
task_expected_mathlib='d13f23b723b8a846827a245b89c10fc7d3f11612'
task_version="$(./lake env lean --version)"
case "$task_version" in
  *"version 4.34.1,"*"commit $task_expected_lean,"*) ;;
  *)
    printf 'Unexpected Lean toolchain: %s\n' "$task_version" >&2
    printf '%s\n' 'Expected Lean 4.34.1 with the commit recorded in README.txt.' >&2
    exit 1
    ;;
esac
task_mathlib_commit="$(git -C .lake/packages/mathlib rev-parse HEAD)"
if [[ "$task_mathlib_commit" != "$task_expected_mathlib" ]]; then
  printf 'Unexpected mathlib commit: %s\n' "$task_mathlib_commit" >&2
  exit 1
fi
if ! git -C .lake/packages/mathlib diff --quiet HEAD --; then
  printf '%s\n' 'The pinned mathlib checkout has tracked modifications; restore it before release verification.' >&2
  exit 1
fi

task_stamp="$(date -u +'%Y%m%dT%H%M%SZ')"
task_log_dir="$task_root/verification-logs/$task_stamp-$$"
mkdir -p -- "$task_log_dir"
printf '%s\n' "$task_version" | tee "$task_log_dir/toolchain.log"
printf 'mathlib commit: %s\n' "$task_mathlib_commit" | tee -a "$task_log_dir/toolchain.log"

task_run_logged() {
  local task_label="$1"
  shift
  printf '\n%s\n' "$task_label"
  "$@" 2>&1 | tee "$task_log_dir/$task_label.log"
}

# Build each computational module alone before building their common importer.
# This avoids launching four memory-intensive proof checks in parallel.
for task_case in 2 3 4 5; do
  task_run_logged "build-case-$task_case" ./lake build "FiniteCase$task_case"
done
task_run_logged build-main ./lake build MainTheorem

# Lake may legitimately reuse an up-to-date .olean. These direct source checks
# always execute the saved-certificate replay again, without deleting caches,
# modifying source timestamps, or overwriting the build's artifacts.
for task_case in 2 3 4 5; do
  task_run_logged "replay-case-$task_case" ./lake env lean "$task_root/FiniteCase$task_case.lean" -DwarningAsError=true
done
task_run_logged replay-main ./lake env lean "$task_root/MainTheorem.lean" -DwarningAsError=true

if grep -w 'sorryAx' "$task_log_dir"/replay-*.log >/dev/null 2>&1; then
  printf '%s\n' 'Verification failed: a final dependency report contains sorryAx.' >&2
  exit 1
fi

printf '\n%s\n' 'Verification succeeded: hashes and pins checked; four certificates and MainTheorem freshly rechecked.'
printf '%s\n' 'Trust includes the standard Lean axioms and compiled bv_check evaluation, as documented in README.txt.'
printf 'Logs: %s\n' "$task_log_dir"
