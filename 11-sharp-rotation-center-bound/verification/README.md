# Verification scope and evidence

The completed claim is the actual planar-composition theorem and its sharpness examples, with the full assumptions in `../SPEC.md`. The principal theorem and literal-formula fixture use a finite list of real angles and complex centers; individual angles are nonnegative and their total is in `(0, pi]`.

All seven mathematical Lean sources retain the checked bytes in `source-freeze.json` and `../lean/SOURCE_SHA256SUMS`. Six files form the theorem dependency closure; `RotationAudit.lean` is a separate exact source-context certificate. Initial direct checks, a separate fresh-output rebuild of the theorem closure and fixture, and a further replay of the portable script passed. The publication-specific replay is also included. Final theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, custom axiom, or native-evaluation oracle is used.

Lean is pinned to 4.32.2, commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`. Mathlib is pinned to `905b95818eb32af7874a58b427f50c1711a5e96c` (v4.32.2); its dependency manifest is included. Existing upstream compiled caches were reused. The reproduction script performs no package downloads and compiles project sources into a newly created output directory, using one thread, 30 seconds per module, and a 3-GiB RSS guard.

The mathematical argument was separately audited before formalization. This is not a claim of external human peer review, an independent proof kernel, a full Mathlib source rebuild, or a fresh-network installation test. The project-authored literal fixture is described as such rather than treated as an external audit.

The three-page publication PDF was rebuilt after removing a stale unpublished-status sentence, then rendered and visually checked. The mathematical assertions and seven Lean sources were unchanged. No overfull or underfull box warning remains.

Compiler diagnostic path prefixes are normalized to `lean/`; messages, theorem statements, axioms, source hashes, exit codes, and resource measurements are unchanged. `SANITIZATION.json` records original and normalized log hashes. No machine-specific execution path or account metadata is intended for publication.

The sharp fixed-angle-list coefficient and directional-width refinement mentioned in the mathematical review are not formalized declarations in this package. No polyhedral unfolding, chain-separation margin, general Dürer solution, or historical novelty is certified by these checks.
