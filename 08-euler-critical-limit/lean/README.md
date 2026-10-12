# Reproducing the critical-limit certificate

## Pinned dependencies

- Official Lean v4.32.2, commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`
- Mathlib v4.32.2, commit `905b95818eb32af7874a58b427f50c1711a5e96c`
- Mathlib dependency lockfile: `mathlib-manifest.json`, SHA-256 `015c7e00ead0f05f2a72b32d9bdef782d4689d05a6297f0ceb0ab5d196c164bd`

Install official Lean/Lake for this toolchain and Git using their official sources. On a machine with network access, prepare a separate upstream checkout:

```sh
git clone https://github.com/leanprover-community/mathlib4.git mathlib4-euler
cd mathlib4-euler
git checkout 905b95818eb32af7874a58b427f50c1711a5e96c
lake exe cache get
```

The checkout's `lean-toolchain` selects Lean v4.32.2 when using elan. Make sure that exact Lean and matching Lake are on PATH when invoking the script below. The supplied Mathlib manifest must match the checkout's `lake-manifest.json`; `build.sh` checks this rather than updating dependencies. No Mathlib source modifications are required. Keep enough disk and memory for the official dependency cache; compilation of a local analytic module may use several GiB.

From any directory:

```sh
export MATHLIB_ROOT=/absolute/path/to/mathlib4-euler
export OUTPUT=/absolute/path/to/new-empty-euler-build
bash /absolute/path/to/08-euler-critical-limit/lean/build.sh
```

The output directory must be empty. The script checks all local source checksums, enforces the pinned Mathlib revision and manifest, checks the Lean version, and builds all twelve local modules in dependency order with one Lean worker. It writes an `.olean` per source and `build.log`, including the axiom audits printed by the sources. Do not publish the generated proof objects as source.

This reproduction script passed against an existing pinned upstream checkout and cache. The fresh-network installation recipe above was not separately tested as part of publication. The upstream cache is a trust boundary: no source rebuild of all of Mathlib or independent-kernel replay is claimed.

## Exact local dependency closure

1. `EndpointWeights.lean`: original binomial weights, positivity, adjacent recurrence, exact endpoint product
2. `ParameterDecay.lean`: logarithmic scaling identity and `p(l)/n(l) -> 0`
3. `BesselSeries.lean`: summability of the explicit factorial series, monotonicity, pointwise continuity
4. `FactorLimit.lean`: endpoint factor bounds and fixed-factor convergence
5. `DenominatorLimit.lean`: zero-extension, finite/tsum equality, endpoint convergence and dominated denominator limit
6. `HarmonicGap.lean`: uniform quadratic harmonic-gap bound including the endpoint
7. `WeightedSeries.lean`: weighted summability and harmonic endpoint-sum convergence
8. `BaselineLimit.lean`: harmonic remainder estimates and baseline convergence
9. `CorrectionLimit.lean`: global residual bound, pointwise decay, summable domination and correction convergence
10. `CriticalLimit.lean`: original coefficient and ratio, exact forward reindexing, numerator decomposition and quotient limit
11. `ExpectedSpec.lean`: explicit intended finite-sum statement and definitional agreement with the general theorem
12. `ConcreteBias.lean`: gamma < 5/8, S1(1)/S0(1) > 5/8, concrete convergence and failure to converge to gamma

The module name `BesselSeries` refers here to an explicit factorial power series. It does not certify a named Bessel-function identity. `SOURCE_SHA256SUMS` covers the twelve unchanged checked sources. All final exported roots depend only on `propext`, `Classical.choice`, and `Quot.sound` in the reported axiom audits. See `../verification/README.md` for the exact evidence and limitations.
