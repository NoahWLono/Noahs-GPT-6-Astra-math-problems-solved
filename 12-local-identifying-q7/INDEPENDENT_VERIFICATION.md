# Completed independent source rebuild

The complete frozen custom proof closure passed its independent rebuild. The final theorem is `ExactCubeCodes.localIdentifying_Q7_optimum24` on the original `ExactCubeCodes.LocalIdentifying` predicate. Its defining proof body, imported interface and explicit original-predicate type ascription passed. The final reported axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Audited evidence

A read-only post-build audit verified:

- All **3,046** frozen Lean sources and **1,444** quoted JSON data hashes.
- All **12,184** current independent object-file hashes, with their original compilation receipt/object identities and direct prerequisite identities.
- All **16** completed stages, with no active compiler operation.
- All **137** designated named-audit modules and **162** expected theorem-audit entries, requiring the correct theorem names and only the standard allowed axioms.
- The final exact-type and axiom logs, reproduced in the [sanitized receipt](checks/INDEPENDENT_VERIFICATION.json).

The final independent state SHA-256 is `a65b5c72f26ad7cabda0dc375896aee3783b3cc3ec4bb20bce59e1279dd5082b`. The runner's final stored status is `paused-at-stage-boundary` because it ends each stage that way; all sixteen stages are complete. Completion is established from the stage/module coverage and successful receipts, rather than that status label alone.

## Reuse and accounting

The independent build did not import custom proof objects from the initial build. Its 3,046 modules consist of:

- **497** modules continued from an earlier phase of the same independent build, after byte-for-byte source/object identity checks.
- **734** C5 modules reused from a separately completed fresh independent C5 rebuild, with their original source/object identities and successful receipts checked.
- **1,815** later fresh independent compilations.

This is a complete independently checked source closure with explicitly documented reuse, rather than a claim that all modules were compiled in a single new invocation. The continued run used **6,503.807440 child CPU seconds**; the earlier independent C5 rebuild used **2,262.154862**, for **8,765.962302** across the distinct independent compilation work. The 497 continued modules are already included in the first total and are not counted twice.

The original C5 aggregate receipt pins source/object identities and stored axiom records. Its per-module logs were reread, matched to those stored audits, and additionally hashed during this post-build audit. Original build state and logs were preserved unchanged. No additional compilation was needed for this audit.

## Public verifier distinction

The completed independent rebuild described above used a separate reviewed orchestration workflow over the frozen sources, with the documented independent-object reuse. A subsequent replay of the unchanged public `verify.py` freshly compiled all **3,046** custom modules with **zero custom-object reuse** and passed the final original-predicate type and named axiom audits. See [public replay evidence](PUBLIC_VERIFICATION.md). The original independent, transport and smoke receipts remain unchanged historical records of their respective checks; their full-verifier status fields describe the evidence available when they were recorded.

Historical priority remains unconfirmed. See PRIOR_ART.md and TRUST.md for the separate literature and computing-base limits.
