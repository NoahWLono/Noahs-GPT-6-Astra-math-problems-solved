#!/usr/bin/env bash
# Optional independent CNF proofs; not a dependency of gpt6_astra/MainTheorem.
set -euo pipefail

proof_dir="$(cd -- "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
workspace_dir="$(cd -- "$proof_dir/../.." && pwd)"
project_dir="$workspace_dir/gpt6_astra"
check_only=false
case "${1:-}" in
  '') ;;
  --check-only) check_only=true ;;
  *) printf 'Usage: %s [--check-only]\n' "$0" >&2; exit 2 ;;
esac
if (( $# > 1 )); then
  printf 'Usage: %s [--check-only]\n' "$0" >&2
  exit 2
fi

required=("$project_dir/lake" "$proof_dir/SharedLRAT.lean" "$proof_dir/DagLRAT.lean")
for weight in 2 3 4 5; do
  required+=("$proof_dir/Anchor${weight}DAG.lean" "$proof_dir/anchor${weight}.lrat"
    "$workspace_dir/research/direct-matrix/case-${weight}-no-pairs-anchor.cnf")
done
for file in "${required[@]}"; do
  if [[ ! -f "$file" ]]; then
    printf 'Required file missing: %s\n' "$file" >&2
    exit 1
  fi
done
if [[ ! -x "$project_dir/lake" ]]; then
  printf 'Project launcher is not executable: %s/lake\n' "$project_dir" >&2
  exit 1
fi

# Capture only Lean's relevant environment after Lake resolves this checkout.
# Lake exits before the large kernel checks, avoiding a retained Lake parent.
# NUL separators preserve spaces; no saved environment or shell eval is used.
env_dir="$(mktemp -d "${TMPDIR:-/tmp}/independent-lean-env.XXXXXXXX")"
trap 'rm -rf -- "$env_dir"' EXIT
(
  cd -- "$project_dir"
  ./lake env bash --noprofile --norc -c '
    for name in PATH LEAN_PATH LEAN_SRC_PATH LEAN_SYSROOT LD_LIBRARY_PATH DYLD_LIBRARY_PATH; do
      if declare -p "$name" >/dev/null 2>&1; then
        printf "%s=%s\0" "$name" "${!name}"
      fi
    done
  '
) > "$env_dir/lean.env"
while IFS= read -r -d '' entry; do
  export "$entry"
done < "$env_dir/lean.env"

# The proof sources deliberately use workspace-root-relative CNF/LRAT paths.
cd -- "$workspace_dir"
lean --version
mathlib_ready=false
IFS=: read -r -a lean_search_dirs <<< "${LEAN_PATH:-}"
for search_dir in "${lean_search_dirs[@]}"; do
  if [[ -f "$search_dir/Mathlib/Tactic/Sat/FromLRAT.olean" ]]; then
    mathlib_ready=true
    break
  fi
done
if [[ $mathlib_ready != true ]]; then
  printf 'Mathlib FromLRAT.olean is unavailable. Prepare the pinned gpt6_astra dependencies first.\n' >&2
  exit 1
fi
printf 'Workspace: %s\nAll required proof inputs and Mathlib FromLRAT are present.\n' "$workspace_dir"
if [[ $check_only == true ]]; then
  printf 'Environment check complete; no Lean proof was rebuilt.\n'
  exit 0
fi

run_dir="$proof_dir/independent-replays/$(date -u +%Y%m%dT%H%M%SZ)-$$"
mkdir -p -- "$run_dir"
export LEAN_PATH="$run_dir:$proof_dir${LEAN_PATH:+:$LEAN_PATH}"
printf 'Sequential proof replay logs and .olean files: %s\n' "$run_dir"
compile_module() {
  local module="$1"
  printf 'Checking %s\n' "$module"
  lean -DwarningAsError=true -R "$proof_dir" "$proof_dir/$module.lean" \
    -o "$run_dir/$module.olean" 2>&1 | tee "$run_dir/$module.log"
}
compile_module SharedLRAT
compile_module DagLRAT
for weight in 2 3 4 5; do
  compile_module "Anchor${weight}DAG"
  expected="'anchor${weight}DagUnsat' depends on axioms: [propext]"
  if ! grep -Fqx -- "$expected" "$run_dir/Anchor${weight}DAG.log"; then
    printf 'Unexpected axiom audit for case %s; inspect its log.\n' "$weight" >&2
    exit 1
  fi
done
printf 'All four original CNFs checked successfully; each axiom audit is [propext].\n'
