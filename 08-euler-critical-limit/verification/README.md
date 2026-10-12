# Verification record

Publication date: 12 October 2026.

## What was checked

The exact public statements are:

1. `EulerScalingAnalytic.tendsto_approximant_critical`: joint critical series-valued convergence of the original finite weighted approximants under only the stated natural-sequence and positive-limit hypotheses.
2. `critical_expected_spec`: the independent explicit finite-sum statement is definitionally the theorem proved by the first root.
3. `EulerScalingAnalytic.tendsto_approximant_pow_two`: convergence for `n(l)=2^l, p(l)=3l` to `criticalLimitOne`.
4. `EulerScalingAnalytic.criticalLimitOne_lt_gamma`: this limit is strictly below Euler's constant.
5. `EulerScalingAnalytic.not_tendsto_approximant_pow_two_gamma`: the same sequence does not converge to Euler's constant.

The local proof closure has twelve modules. All public Lean source bytes match the checked source closure; the source checksums are in `../lean/SOURCE_SHA256SUMS`.

## Compiler evidence

- `rebuild.log`: earlier independent fresh-output compilation of the first ten modules through `CriticalLimit`.
- `expected-spec.log`: independent compilation and axiom audit for the explicit statement fixture.
- `concrete-bias.log`: independent compilation and axiom audits for the concrete limit, strict gap and failure to converge to gamma.
- `publication-rebuild.log`: a further fresh-output rebuild of all twelve unchanged publication sources using the public `lean/build.sh` script.

All these runs used official Lean 4.32.2 and Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`. Pinned upstream compiled dependency caches were reused. No existing local proof `.olean` files were used in the publication rebuild. Every module was compiled anew in dependency order. The final roots' axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.

The source review found no `sorry`, `admit`, custom axiom, `unsafe`, `native_decide`, `implemented_by`, or evaluation shortcut. Import review confirmed the complete local dependency closure and Mathlib imports. A separate read-only source/manuscript review checked the original finite-sum semantics, zero-extension, derived parameter decay, uniform-in-index domination and the correction bound. It independently recomputed the rational constants in the concrete strict-gap proof. This review was not an independent-kernel verification or a new bibliography audit.

## Public paper

The scoped public paper replaces the broader research manuscript's quantitative/surviving-regime presentation with a direct endpoint and dominated-convergence proof of the two certified results. The mathematical definitions and completed theorem scope are unchanged. The twelve Lean sources are unchanged. The public PDF was rebuilt from the supplied LaTeX and visually reviewed on all five pages. No numerical experiment is required for the theorems.

## Limits

- No separate-kernel export/replay was performed.
- No source rebuild of all of Mathlib was performed; cached official upstream dependencies were reused.
- The public build script passed with the existing pinned checkout/cache; a fresh-network installation was not separately tested.
- Mathematical checking does not establish historical novelty, and no external human peer review is claimed.
- The Bessel identification, a strict gap for every positive limit parameter, the quantitative finite-parameter estimate and the diverging-parameter regime are outside the completed public theorem scope.
- Euler's constant is not proved irrational. No improved arithmetic approximation or denominator-quality conclusion is established.
