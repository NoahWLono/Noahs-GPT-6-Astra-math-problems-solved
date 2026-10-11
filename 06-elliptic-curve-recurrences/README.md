# ASTRA-01: elliptic-curve rational recurrence obstructions

This package contains a research note and Lean 4 verification of its main obstruction theorems and mathematical examples. It does not provide an ECDLP-solving algorithm or establish historical novelty.

- [Formal verification addendum, 11 October 2026](FORMAL_VERIFICATION.md), [PDF](FORMAL_VERIFICATION.pdf), and [LaTeX source](FORMAL_VERIFICATION.tex)
- [Original manuscript (PDF)](original-research/manuscript.pdf) and [TeX source](original-research/manuscript.tex)
- [Lean proofs and exact coverage](lean/README.md)
- [Reproduction instructions](lean/LOCAL_REPRODUCTION.md)
- [Independent novelty review](reviews/06-independent-novelty-review.md)
- [Byte-preservation manifest for all 24 original assets](ORIGINAL_ASSET_MANIFEST.json)

The original research snapshot is preserved unchanged under original-research/. Its statements that proof-assistant verification had not been performed describe that earlier snapshot. The dated addendum supersedes that historical status for the precise Lean endpoints it lists. It does not supersede the original cautions about novelty, general cryptographic algorithms or runtime lower bounds.

The main bound counts projective recurrence agreements, including poles: at most min(n,D(r+1)) for a single rational update, and the corresponding finite-menu union bound. Global identities force degree one and n dividing D. The finite-field and full prime-group obstructions use actual PGL elements. Exact finite examples delimit these results; they do not imply an efficient branch selector or cryptographic attack.
