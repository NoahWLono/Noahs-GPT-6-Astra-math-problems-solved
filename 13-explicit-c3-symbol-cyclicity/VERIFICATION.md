# Verification record

## Initial theorem check: passed

The initial complete source chain and final `PrimeFiveFamily.symbolFamily_cyclicity` theorem checked with official Lean 4.32.2 and Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`. The final theorem has no additional power premise. The source closure consists of 729 arithmetic modules and 34 structural/family/final/audit modules, for 763 total including `FinalAudit`.

The exact final statements and named axiom audit are preserved in [verification/initial-final-audit.txt](verification/initial-final-audit.txt). Final cyclicity depends only on `propext`, `Classical.choice`, and `Quot.sound`; literal output alignment depends on no axioms. Exact saved arithmetic is checked inside Lean and is not accepted merely as an external solver or Python answer.

## Staged independent replay: passed

The completed final replay freshly compiled all 418 N5 modules (including both required pilot modules), a separate N5 audit, and `FrozenCentralOutput75`, `FinalAssembly`, and `FinalAudit`. All 422 invocations passed, with zero failures or retries. The final theorem and exact axiom report passed against these fresh final outputs; source and object hashes were verified. The final theorem has no additional fifth-power hypothesis and depends only on the three standard Lean axioms.

Its precise reuse boundary is:

- 212 N4 modules reused from their completed independent fresh rebuild
- 31 structural modules reused from the earlier independent structural rebuild (that earlier run checked 34 modules through a conditional endpoint)
- 99 original earlier base/N2/N3 module objects reused, explicitly hash-verified
- `modern.Algebra` and `modern.Numerator`, among those 99, also had separate source rebuilds; the remaining 97 retain original checked-object provenance

The 763-source archive partitions as 418 fresh N5 + 3 fresh support/final/audit + 212 previously fresh N4 + 31 previously fresh structural + 99 original earlier modules. The additional standalone N5 replay audit is included separately as `verification/N5ReplayAudit.lean`. No original N5 object or original-project loader fallback was used. This is a staged replay with disclosed project-object reuse, not a zero-reuse or fresh end-to-end rebuild of every custom source.

The final run used 3348.363222 actual child CPU seconds: 3338.768295 for N5 plus its audit and 9.594927 for the final three modules. The terminal receipt, normalized compiler receipts, module provenance inventory and exact final axiom/statement output are included:

- [Terminal summary](verification/staged-replay-summary.json)
- [763-source provenance inventory](verification/staged-source-inventory.json)
- [Fresh/reused module lists](verification/staged-replay-modules.json)
- [422 compiler receipts](verification/staged-compile-receipts.json)
- [Final theorem and axiom audit](verification/staged-final-audit.txt)
- [N5 identity audit](verification/staged-n5-audit.txt)

The raw runner's `fresh` import flag classified only names beginning `modern.N5`; it is not an authoritative freshness classification for final-family modules. The terminal reconciliation verified all four fresh `FinalAssembly` output hashes against the `FinalAudit` imports. The public receipts omit that misleading flag; the module inventory above supplies the actual provenance. Only machine-local paths and storage metadata were omitted or normalized; mathematical source bytes and the exact statement logs are unchanged.

## Public transport and verifier checks

Archive safety, all 763 source hashes, exact source-count/byte totals, topological import order and readable-source equality are checked by `lean/verify.py --check-only`. Python syntax, CLI and supplementary exact-arithmetic checks passed without starting a Lean build. A local dependency preflight verified the compiler version, Mathlib revision, lock and all eight dependency revisions, then correctly stopped at missing upstream objects in the main Mathlib output tree. The original runs use separately prepared pinned-upstream objects for `Mathlib.FieldTheory.KummerExtension` and `Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`; the public recipe instead builds the complete pinned dependencies into the standard Mathlib output tree. This local preflight is not a successful full build. The new public wrapper has not yet completed an end-to-end compilation. It is a reproducible route, not evidence of a replay that did not occur.

The archive SHA256 is `e24f4949b55bec86558c1c79e67d9a854c2344d96827593a781872461d940f3b`. Its source-manifest SHA256 is `4e61ffa5622ae64508003caf9beb58305380866167dca5bd3294a7f97e9678d6`.

## Trust and review limits

The existing checks reuse pinned upstream Lean/Mathlib dependencies. They do not claim a whole-Mathlib source rebuild, an independent kernel implementation, a fresh-network installation test, cross-platform validation, or external human peer review. The source-only instructions also explain how to build upstream dependencies from source. The Python exact-arithmetic replay is corroborating evidence, not a proof axiom.

The final manuscript was rebuilt after the terminal replay and its source/provenance wording was reconciled with these records. The final rendering review and exact PDF hash are recorded in `verification/editorial-qa.json`. Historical novelty remains unestablished regardless of verification outcome.
