#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
: "${MATHLIB_ROOT:?Set MATHLIB_ROOT to the pinned Mathlib checkout with official cached dependencies.}"
export MATHLIB_ROOT
EXPECTED=905b95818eb32af7874a58b427f50c1711a5e96c
[[ "$(git -C "$MATHLIB_ROOT" rev-parse HEAD)" == "$EXPECTED" ]] || { echo 'Mathlib revision mismatch'; exit 2; }
lean --version | grep -F 'version 4.32.2,' >/dev/null
mkdir -p "$ROOT/build"
for module in ZariskiBasic ZariskiDifference ZariskiActions ZariskiFibres ZariskiEscape ZariskiTransitivity ZariskiOriginal ZariskiComplexClosure ZariskiPolynomiality ZariskiMain ZariskiExpected; do
  python3 "$ROOT/lean/check_one.py" "$module" 60
done
if grep -E 'sorryAx|error:' "$ROOT/build/"Zariski*.log; then exit 3; fi
