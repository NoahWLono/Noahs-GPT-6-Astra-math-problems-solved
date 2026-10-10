# Adaptive progressive verification with short private check banks

This completed research package contains a new, narrowly scoped verification method, its detailed paper, and a finite Lean proof. It changes private verification preprocessing and checking, not signature generation. The combined method and quantified tradeoff passed a qualified prior-work review; no claim of universal priority, a new signature primitive, or practical speedup is made.

## Result

For independent secret projection rows over a finite field of size q, an observer may make L adaptive chosen-row zero/nonzero queries. For a subsequently chosen nonzero residual, the probability that at least u of s rows vanish is at most

    delta = choose(L+s,u) / (q-L-s)^u,  provided L+s < q.

Fresh random row-index sampling after the final candidate and threshold T are fixed gives additional invalid-acceptance probability at most

    E[((u-1)/s)^T] + E_max * delta.

A separate joint-threshold event bound is proved. E_max is a deterministic maximum epoch allowance. This is an aggregate/joint experiment guarantee, not posterior reliability for every transcript. The compiled finite machine executes stored matrix checks, incremental preparation, actual buffer promotion, reserved aborted/zero-check calls, and a separately charged final invocation. Trace-erased refinement removes proof traces and obsolete buffer copies.

For N invocations and S executed row checks, its exact initialized multiplication count is B+NW+(m+n)S, where B=snm=RW. The finite example has a narrow early field-arithmetic crossing against specified terminal and code-sampling baselines. A three-row terminal configuration already meets the weak targets after three row checks, so the initialized pool advantage against it concerns only the first two nominal checkpoints. Nominal depth b has error cap 2^-b plus an explicit history term. This is not an optimality claim.

## What is validated

- 67 Lean modules independently rebuilt from source.
- 862 theorem declarations exhaustively audited for standard Lean axioms only.
- Independent endpoint semantic review and paper mathematical review passed the stated scope.
- A separate novelty/comparison review passed a qualified combined-method claim, crediting known probability and preprocessing ingredients.
- The reviewed 14-page PDF was rendered and every page visually inspected.

The field-arithmetic schedule does not cover all work: ideal random-sampling bursts, dense-array zero initialization, memory traffic, allocation, cursor integer decoding, original hashing/norm checks and real machine costs remain explicit. The retained-field inventory is not a total runtime memory bound, and retains A. A practical benefit remains an empirical question.

The theorem assumes ideal finite sampling and serialized atomic invocations. It does not cover field-value leakage, timing leakage, faults, rollback, exposed checking keys, or arbitrary resumed/forked final sessions. Finite independent rational random-tape mixtures are included. Ordinary source-signature security is a separate named assumption, not a proved EUF simulation or lattice-hardness reduction. The numerical point is not a recommended secure signature parameter set.

## Files

- `paper/short-private-pools.pdf`: reviewed paper.
- `paper/short-private-pools.tex`, `paper/build.sh`: editable source and standard two-pass build.
- `lean/`: exact frozen V2 source files and original manifest/build controls. Frozen STATUS/README statements that review was pending are superseded only by `POST-AUDIT-V2.md` and completed reports.
- `reproduction/README.md`: pinned dependency setup and portable source-only build plus exhaustive axiom audit.
- `reproduction/REPORT.md`: completed independent build evidence.
- `reviews/`: endpoint, paper-math and novelty/comparison review records, with final-pass addenda.
- `SHA256SUMS`: all package files except itself.

The paper's Appendix A maps mathematical claims to Lean entry points. Start with `ProgressivePool.FinalTraceErasure.final_signature_bound`, `final_signature_joint`, `finalMachine_total_multiplications` and `finalMachine_perfect_completeness`.

Reviewed paper source SHA-256: `b305c71785d72c8d91d585e738e9d9ba0cbe1e4570e19573c1fb7d0b1d608d33`.
Frozen Lean manifest SHA-256: `218087b2b1b3961c6a275095e27ca46ec2d42cbb88798732c6f7ea3d7546296d`.

No failed construction attempts, project `.olean` files, dependency binaries or build caches are part of this package. Research and proof assistance should not be confused with a human peer-review or independent source-hardness certification.
