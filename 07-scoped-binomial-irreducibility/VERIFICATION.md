# Verification results and limits

This report summarizes the completed checks of the exact mathematical sources published here. Publication preparation checked file integrity and source correspondence; it did not repeat the Lean builds or independent proof-checker runs described below.

## Original prime-inner-exponent theorem

Root: `PillaiScoped.irreducible_composition_of_prime_valuation_bounds`.

- The 51 production modules and declaration audit compiled with Lean 4.32.2 and pinned Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`.
- The production theorem type and referenced definitions matched a separately authored, reviewed requested-type specification.
- The complete serialized proof dependency closure passed patched official Lean 4.34.1 kernel replay and independent nanoda 0.4.19 checking: 45,192 declarations.
- Production axioms were exactly `propext`, `Classical.choice`, and `Quot.sound`; production did not contain `sorryAx`.
- All 51 production modules and the audit were subsequently rebuilt from the packaged source bytes into an empty output tree using pinned upstream caches. All 52 output objects matched the validated objects. An export from those fresh objects was byte-identical to the validated 294,553,707-byte closure.
- Production export SHA-256: `e708c9c22e754d2af9b542fd151819c37fa5c00bb169f4acc4c934e573d10652`.
- The original 41 recursive standard-axiom audits passed.

## Composite-inner-exponent extension

Root: `PillaiScoped.irreducible_composition_of_inner_prime_factors_gt`.

- The new root and its five-declaration audit compiled with Lean 4.32.2 in the inherited pinned dependency environment.
- An independent AI-assisted review of the exact source and printed endpoint passed.
- Requested-type and referenced-definition comparison passed. Its complete serialized dependency closure passed patched official Lean 4.34.1 kernel replay and independent nanoda 0.4.19 checking: 45,387 declarations.
- All 26 mandatory primitives and the types of present permitted axioms matched a separately generated trusted official Lean 4.32.2 baseline.
- All five audited declarations and the production closure used exactly `propext`, `Classical.choice`, and `Quot.sound`; production did not contain `sorryAx`.
- Production export size: 295,701,911 bytes. SHA-256: `dbdd3d7070ddbe3a596e4831e56659a198270db6c98c85f0976909081e90552d`.
- The 4,527 expected imported-object hashes matched a source-completed inventory. This was not a fresh runtime module enumeration. No new whole-source clean rebuild is claimed for the extension.

## Trust boundary

These were non-isolated validation-adapter checks, not sandboxed comparator certification, verification of the checker implementations, or external human peer review. Separate unproved statement fixtures were used only for type comparison and were not production proof dependencies. They are not included here.

The original clean-local rebuild reused pinned upstream caches. It did not test a fresh-network dependency installation. The portable installation instructions and the publication-adapted manifest readers have not been exercised as a new complete Lean build in this publication environment. The read-only source preflight passed against all 121 original source hashes and the closed local import order after adaptation.

The public report preserves the verified outcomes and their limitations without distributing historical machine-specific execution records. It is a summary of the recorded checks, not a replacement proof-checker certificate. The large serialized exports, checker executables, dependency checkouts, and compiled proof objects are not distributed.

Formal correctness of these scoped statements, historical originality, and the full fixed-gap Pillai conjecture are distinct questions. Historical novelty remains unestablished and the full conjecture remains unresolved.
