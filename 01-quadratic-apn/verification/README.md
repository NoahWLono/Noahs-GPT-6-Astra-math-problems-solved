# Verification status

**PASS:** all 136 local proof modules were freshly rebuilt from isolated source snapshots on 9 October 2026. No source changed after the snapshots. Every final endpoint has precisely `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. No proof holes, custom axioms, or `native_decide` occur in the comment-stripped source scan.

See [the complete audit](AUDIT.md), [module results](results.json), [final axiom output](logs/APNEightFinal.log), and [source hashes](source-manifest.json). Total summed compiler time was 579.965 seconds; maximum observed RSS was 2,156,332 KiB.

The portable publication wrapper passed source-hash/dependency-order checks for all 137 modules and freshly compiled its first five modules in a smoke test. It was stopped during module six to avoid duplicating the full audit. This is not a completed fresh network bootstrap or full run of that wrapper. The optional endpoint-inspection file is additional to the 136-module proof closure.

Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned. The standard library and upstream mathlib are reused as installed; this is not a rebuild or independent implementation of the prover itself. Machine-specific path prefixes were sanitized for publication; source and proof-output content were not changed.

## Additional endpoint inspection

`APNEightFinalAudit` was separately compiled against the fresh independent outputs with exit 0. Its statement/definition inspection and final axiom report are in [the endpoint audit log](logs/APNEightFinalAudit.log); [the result](endpoint-audit-result.json) records 2.108 seconds and 1,971,200 KiB peak RSS. This extra check leaves the original 136-module rebuild result unchanged. The publication wrapper rebuilds this inspection module as its final step.
