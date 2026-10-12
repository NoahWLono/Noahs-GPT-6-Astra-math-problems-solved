#!/usr/bin/env bash
# Rebuild every local proof source in a fresh directory with fixed resource guards.
set -euo pipefail
SOURCE=$(cd -- "$(dirname -- "$0")" && pwd)
: "${MATHLIB_ROOT:?Set MATHLIB_ROOT to the pinned Mathlib checkout}"
: "${OUTPUT:?Set OUTPUT to a fresh, empty output directory}"
export MATHLIB_ROOT=$(cd -- "$MATHLIB_ROOT" && pwd)
mkdir -p -- "$OUTPUT"
export OUTPUT=$(cd -- "$OUTPUT" && pwd)
if [[ -n "$(find "$OUTPUT" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
  echo 'OUTPUT must be empty; existing project proof objects must not be reused.' >&2
  exit 1
fi
export LEAN_BINARY=${LEAN_BINARY:-$(command -v lean)}
export LEAN_BINARY=$(cd -- "$(dirname -- "$LEAN_BINARY")" && pwd)/$(basename -- "$LEAN_BINARY")
export PATH="$(dirname -- "$LEAN_BINARY"):$PATH"
[[ "$(git -C "$MATHLIB_ROOT" rev-parse HEAD)" == 905b95818eb32af7874a58b427f50c1711a5e96c ]]
cmp "$SOURCE/mathlib-manifest.json" "$MATHLIB_ROOT/lake-manifest.json"
(cd "$SOURCE" && sha256sum -c SOURCE_SHA256SUMS)
(cd "$MATHLIB_ROOT" && "$LEAN_BINARY" --version) | grep -F 'version 4.32.2,' >/dev/null
(cd "$MATHLIB_ROOT" && "$LEAN_BINARY" --version) | grep -F 'commit f3b06c705e6c85f5314019d5d3baab0fec5b580c' >/dev/null
modules=(NakaiFramework QuarticDefinitions QuarticCofactors QuarticCoefficientDefinitions QuarticDeterminant QuarticSeparatorMonomials QuarticSeparatorValue QuarticSeparatorAnnihilation QuarticSeparator QuarticOperatorCoefficients QuarticOperatorDescent QuarticPolynomial QuarticOperatorOrder NakaiConcrete NakaiExpected)
{
  (cd "$MATHLIB_ROOT" && "$LEAN_BINARY" --version)
  printf 'Mathlib revision: %s\n' "$(git -C "$MATHLIB_ROOT" rev-parse HEAD)"
  printf 'All fifteen local modules are rebuilt; upstream dependency caches are reused.\n'
  for module in "${modules[@]}"; do
    printf '\nBUILD %s\n' "$module"
    python3 "$SOURCE/check_one.py" "$module" replay
    printf 'PASS %s\n' "$module"
  done
  printf '\nPASS all 15 local modules\n'
} 2>&1 | tee "$OUTPUT/build.log"
