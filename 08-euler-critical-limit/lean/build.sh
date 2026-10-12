#!/usr/bin/env bash
# Compile every local source into a fresh output directory using pinned upstream dependencies.
set -euo pipefail
SOURCE=$(cd -- "$(dirname -- "$0")" && pwd)
: "${MATHLIB_ROOT:?Set MATHLIB_ROOT to the pinned Mathlib checkout}"
: "${OUTPUT:?Set OUTPUT to a fresh, empty output directory}"
MATHLIB_ROOT=$(cd -- "$MATHLIB_ROOT" && pwd)
mkdir -p -- "$OUTPUT"
OUTPUT=$(cd -- "$OUTPUT" && pwd)
if [[ -n "$(find "$OUTPUT" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
  echo 'OUTPUT must be empty; existing proof objects must not be reused.' >&2
  exit 1
fi
[[ "$(git -C "$MATHLIB_ROOT" rev-parse HEAD)" == 905b95818eb32af7874a58b427f50c1711a5e96c ]]
cmp "$SOURCE/mathlib-manifest.json" "$MATHLIB_ROOT/lake-manifest.json"
(cd "$SOURCE" && sha256sum -c SOURCE_SHA256SUMS)
cd "$MATHLIB_ROOT"
lean --version | grep -F '4.32.2'
export LEAN_NUM_THREADS=1
export LEAN_PATH="$OUTPUT:$(lake env printenv LEAN_PATH)"
modules=(EndpointWeights ParameterDecay BesselSeries FactorLimit DenominatorLimit HarmonicGap WeightedSeries BaselineLimit CorrectionLimit CriticalLimit ExpectedSpec ConcreteBias)
{
  lean --version
  printf 'Mathlib revision: %s\n' "$(git rev-parse HEAD)"
  printf 'All twelve local modules are rebuilt from source. Upstream caches are reused.\n'
  for module in "${modules[@]}"; do
    printf '\nBUILD %s\n' "$module"
    lean -M4096 --root="$SOURCE" -o "$OUTPUT/$module.olean" "$SOURCE/$module.lean"
    printf 'PASS %s\n' "$module"
  done
  printf '\nPASS all 12 local modules\n'
} 2>&1 | tee "$OUTPUT/build.log"
