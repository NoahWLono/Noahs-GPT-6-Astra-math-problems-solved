# Critical scaling of iterated rational approximants to Euler's constant

**Completed scoped results, verified in Lean. Historical novelty remains unresolved. Euler's constant is not proved irrational.**

[Read the mathematical paper](paper/euler-critical-limit.pdf) · [LaTeX source](paper/euler-critical-limit.tex) · [Reproduce the proof](lean/README.md) · [Verification record](verification/README.md) · [Prior-art review](reviews/prior-art-review.md)

## Exact completed result

For natural-valued sequences `n(l), p(l)` with `n(l) >= 1`, `n(l) -> infinity`, and `n(l)^3 / 2^p(l) -> lambda0 > 0`, the original weighted approximant

- `w(n,p,k) = choose(n,k)^2 * choose(n+k,k)^p / k!`
- `a(n,p,k) = (p+3) H_k - 2 H_(n-k) - p H_(n+k)`
- `R(n,p) = sum(k=0..n, w(n,p,k)*a(n,p,k)) / sum(k=0..n, w(n,p,k))`

converges to `3 gamma + log(lambda0) - 2 S1(lambda0)/S0(lambda0)`, where

- `S0(x) = sum(j>=0, x^j/(j!)^2)`
- `S1(x) = sum(j>=0, H_j*x^j/(j!)^2)`.

For the explicit sequence `n(l)=2^l, p(l)=3l`, the parameter is identically one. The sequence converges to `3 gamma - 2 S1(1)/S0(1)`, and the certificate proves this limit is strictly less than gamma. It therefore does not converge to gamma.

The theorem derives parameter decay, summability, pointwise convergence, uniform-in-index domination, the denominator limit, numerator decomposition and quotient limit. None is a separate hypothesis of the final result. [ExpectedSpec.lean](lean/ExpectedSpec.lean) spells out the original finite sums and limit series and checks the exact intended statement against the exported theorem. [ConcreteBias.lean](lean/ConcreteBias.lean) proves the concrete strict gap by rational bounds without a Bessel identity.

## Scope and trust boundary

All twelve local Lean sources were rebuilt into fresh output directories using official Lean 4.32.2 and pinned Mathlib v4.32.2. Upstream dependency caches were reused. The exported theorem audits list only `propext`, `Classical.choice`, and `Quot.sound`. There are no admitted proofs, custom axioms, unsafe declarations, native-evaluation proof shortcuts, or implementation overrides in these sources. No separate-kernel export/replay or external human peer review is claimed.

The established approximant family and classical Bessel ingredients are not claimed as new. The [review](reviews/prior-art-review.md) records checked primary-source versions, theorem-scope comparisons and access/coverage gaps. Correctness and originality are separate questions.

The public paper is limited to the critical series-valued limit and its concrete non-gamma example. It does not include the earlier broader quantitative finite-parameter estimate or diverging-parameter regime as completed results. The Bessel identification and strict gap for every positive parameter are outside this formal certificate. No irrationality, arithmetic-quality improvement, or priority claim is made.

## Package

- `paper/`: scoped manuscript, PDF and portable two-pass build script
- `lean/`: unchanged twelve-module proof closure, pinned toolchain/manifest, source checksums, build instructions and script
- `verification/`: compiler output from independent and publication-source rebuilds, with a concise verification record
- `reviews/`: bounded prior-art comparison and explicit originality limitations
- `SHA256SUMS`: every public package file except the manifest itself

Compiled proof objects, dependency checkouts, private research notes, temporary experiments and machine-specific execution metadata are not distributed. The paper and proof are usable independently of the original research snapshot.
