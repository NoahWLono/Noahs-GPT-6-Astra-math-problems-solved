#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
: "${NAKAI_BUILD_DIR:?Choose a fresh, empty output directory}"
: "${MATHLIB_ROOT:?Path to the pinned cached mathlib checkout}"
export MATHLIB_ROOT
: "${LEAN_BINARY:?Path to the pinned Lean binary}"
export LEAN_BINARY
[[ "$(git -C "$MATHLIB_ROOT" rev-parse HEAD)" == 905b95818eb32af7874a58b427f50c1711a5e96c ]]
"$LEAN_BINARY" --version | grep -F 'version 4.32.2,' >/dev/null
"$LEAN_BINARY" --version | grep -F 'commit f3b06c705e6c85f5314019d5d3baab0fec5b580c' >/dev/null
if [[ -d "$NAKAI_BUILD_DIR" ]] && [[ -n "$(find "$NAKAI_BUILD_DIR" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
  echo 'Output must be empty; existing files will not be deleted.' >&2; exit 1
fi
(cd "$ROOT" && sha256sum -c SOURCE_SHA256SUMS)
cmp "$ROOT/upstream/EulerIdentity.lean" "$MATHLIB_ROOT/Mathlib/RingTheory/MvPolynomial/EulerIdentity.lean"
python3 "$ROOT/build/prepare_overlay.py"
python3 "$ROOT/build/check_euler_upstream.py" replay
for module in NakaiFramework NakaiJacobi NakaiHomogeneousDefinitions NakaiHomogeneousEuler NakaiHomogeneousDescent NakaiHomogeneousEscape NakaiHomogeneousConditional NakaiVariableSyzygy NakaiDeterminantRow NakaiHomogeneousDeterminant NakaiPurePowers NakaiHomogeneousCoefficients NakaiFiniteQuotient NakaiHessianFinite NakaiHomogeneousFinite NakaiHomogeneousFiniteExpected; do
  python3 "$ROOT/build/check_framework.py" "$module" replay
done
