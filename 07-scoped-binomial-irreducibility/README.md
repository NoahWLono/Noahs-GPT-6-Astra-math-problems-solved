# Scoped irreducibility of shifted binomial compositions

**Completed scoped results, verified in Lean. Historical novelty is unestablished. The full fixed-gap Pillai conjecture remains unresolved.**

Let `p >= 5` be prime, let `k, A` be integers with `|k| > 1`, and suppose `v_ell(k) < p` for every prime `ell` dividing `k`. The original paper proves that `(X^q - A)^p + k` is irreducible over the rationals for every prime `q > p`. The addendum proves the same conclusion for `(X^m - A)^p + k` whenever `m > 1` and every prime divisor of `m` exceeds `p`.

Repeated prime factors of `m` are allowed. The signs of `A` and `k` are unrestricted, `A = 0` is permitted, and no coprimality condition on `m` and `k` is imposed. These are auxiliary irreducibility results, not a solution of the full fixed-gap Pillai conjecture or a novelty claim.

## Read the papers

- [Original 12-page paper](original/paper/scoped-binomial-irreducibility.pdf) and [unchanged LaTeX source](original/paper/scoped-binomial-irreducibility.tex)
- [Three-page composite-inner-exponent addendum](addendum/composite-inner-addendum.pdf) and [unchanged LaTeX source](addendum/composite-inner-addendum.tex)
- [Original Lean sources and reproduction instructions](original/lean/README.md)
- [Extension sources, theorem map and reproduction instructions](addendum/README.md)
- [Verification results and assurance limits](VERIFICATION.md)
- [Publication format and PDF integrity](PUBLICATION_FORMAT.md)

The exact roots are `PillaiScoped.irreducible_composition_of_prime_valuation_bounds` and `PillaiScoped.irreducible_composition_of_inner_prime_factors_gt`. All 54 local Lean proof/audit sources and 70 pinned upstream source copies are unchanged from the verified source packages. Their third-party license notices are retained.

## Download and reproduce

The [original public source package](source-bundles/scoped-irreducibility-public-20261012.zip) and [addendum public source package](source-bundles/composite-inner-addendum-public-20261012.zip) contain the corresponding paper, LaTeX and Lean sources, with the public verification report. These are newly assembled publication packages, not the historical sealed archives named in the papers. Machine-specific execution records are omitted; mathematical sources are unchanged.

Run `sha256sum -c SHA256SUMS` from this folder before reproduction. Then follow the original Lean instructions and use that rebuilt dependency environment for the additive extension. The compiler is Lean 4.32.2 and Mathlib is pinned to `905b95818eb32af7874a58b427f50c1711a5e96c`.

Both exact roots passed separately authored requested-type comparison and full serialized dependency-closure checking with a patched official Lean 4.34.1 kernel and independent nanoda 0.4.19, using exactly `propext`, `Classical.choice`, and `Quot.sound`. The original sources also passed an all-local rebuild against pinned upstream caches. The checking used a non-isolated adapter; it is not external human peer review. A fresh-network dependency installation has not been independently tested. Publication preparation did not rerun Lean or the proof checkers.

The materials were prepared with AI assistance. The owner's project-series label does not certify runtime model identity, affiliation, or peer review.
