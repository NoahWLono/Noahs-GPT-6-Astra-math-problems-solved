# Independent frozen V2 progressive-verifier audit

## Result

PASS: all 67 selected modules compiled from source with exit 0; all 862 theorem declarations defined by those modules passed transitive standard-axiom checks. All 72 input hashes verified before and after compilation. The original author directory also still matches the frozen manifest after this run. No source was edited and no author project `.olean` was reused.

## Frozen scope and method

This audit targets the 67 Lean modules and 72 files listed in `source/SOURCE-SHA256SUMS-v2`, SHA-256 `218087b2b1b3961c6a275095e27ca46ec2d42cbb88798732c6f7ea3d7546296d`. Only manifest files were copied to the new independent directory; no author `.olean` files were copied. The previous 32-module audit was preserved unchanged.

The manifest includes the exact README-v2.md and STATUS.md scope statements reviewed here. Individual file SHA-256 values are retained in the source manifest, and `hash-verification.log` records verification. The selected project files are immutable audit inputs, not the author's ongoing directory.

Compiler: Lean 4.19.0 release commit `6caaee842e94`. Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Existing pinned toolchain and mathlib dependency binaries are trusted/reused, not independently bootstrapped. `environment.json` records the precise LEAN_PATH; the original author's project directory is absent. Every project import is checked to precede its user in the manifest (`dependency-order.txt`).

`rebuild.py` runs source-first with a separate output `.olean` for each selected source, one Lean worker, a 2 MiB stack and MALLOC_ARENA_MAX=2. It takes the existing shared `.lean-compile.lock`, bounds each compilation to 120 seconds, and polls RSS every 50 ms with a 2,900,000 KiB cap (stricter than 2.9 GiB). Termination has a three-second grace before forced kill. Logs retain exact exit codes, sampled RSS, elapsed times, warnings and any limit event.

The copied build-all-v2.sh and check.sh are unchanged. Their relative toolchain-location assumption does not fit the new independent directory; the independent runner explicitly resolves that location while retaining the bounded compiler settings. To reproduce under this workspace, create another sibling of this audit directory under independent-build, copy the manifest files into source/ plus the auditor's AuditAxioms.lean, create logs/, copy rebuild.py to the new root, and run `python3 rebuild.py`. Do not copy any project `.olean`. AUDIT_ONLY=1 checks theorems against an already rebuilt snapshot.

## Trust audit

The auditor imports exactly the 67 listed modules, identifies declarations by their defining module IDs rather than a name prefix, and runs Lean's kernel-environment transitive `collectAxioms` on every theorem declaration, including private/anonymous/generated theorem declarations. It fails on anything other than propext, Classical.choice or Quot.sound. It does not permit sorryAx, native-decision proof axioms, lcProof, or project-specific axioms in any theorem's dependency closure.

This is intentionally an all-theorem audit. Compiler-generated non-theorem LCNF artifacts can contain Lean's internal proof-erasure placeholder, which is not permission to accept it in a theorem. No author-written proof is excluded. A separate comment-stripped source scan checks all selected files for sorry, admit, axiom, native_decide, unsafe, extern, implemented_by, and trustLevel; see trust-token-check.json. Regular `decide` and proof-producing arithmetic tactics are permitted and kernel checked.

## Exact final-machine theorem assumptions

All names below have prefix ProgressivePool.FinalTraceErasure.

### final_signature_bound and final_signature_joint

These theorems bound the finite probability mass defined using the trace-erased finalMachine's actual accepted Boolean, its output's nonzero matrix residual, and the optional selected event. The aggregate result is E[rho^T] + (phases.length+1)*delta, with rho=(u-1)/s and delta=choose(R*k+s,u)/(q-R*k-s)^u. The joint version is rho^t*Pr[T=t] plus the same additive term. It is not a conditional guarantee after conditioning on a rare threshold event.

Explicit hypotheses:

- finite field F, finite-cardinality instance and decidable equality;
- positive s and u, and a supplied nonzero dummy residual;
- dense matrix A with dimensions n by m and exact preparation budget s*m*n=R*W;
- a finite list of prior phases, plus a terminal phase of reservation bound r with r+1≤R;
- `ConditionalFull` for every phase: for every history and current bank, a continuing branch executes exactly R reservations; a stopping branch executes at most R-1, leaving the final slot;
- every prior and terminal invocation tree has at most k row tests, for every history;
- field margin R*k+s<card F.

The sample space is the defined finite product of independent uniform checking banks. Final index functions are explicitly uniform fresh functions Fin(T draws)→Fin s, so draws are with replacement and their length is chosen first. T may be an arbitrary function of the prior modeled bank draws; the theorem itself does not require T≤k. The separately proved VerifierInterface wrapper clamps user requests to min(requested,k). The final candidate is a fixed function of the history output. Future prefetch cannot influence the output through the admitted phase interface; this is model-level noninterference, not a timing-leakage claim.

No source-signature hardness hypothesis is needed for the *additional verification-error* endpoints. Combining with ordinary forgery security is a separate theorem in StoppedSourceBound, whose OrdinarySourceBound premise explicitly assumes the ordinary fresh-valid forgery mass is bounded. That theorem is not an EUF simulation or a new hardness reduction.

### finalMachine_total_multiplications

Requires the finite field infrastructure, exact s*m*n=R*W, ConditionalFull for all prior phases, and r+1≤R. For the actual trace-erased result e it proves:

    e.preparationMultiplications + e.checkingMultiplications
      = s*m*n + e.reservations*W + (m+n)*e.checks.

Reservations and checks include the designated final call. Setup, incomplete last phases, zero-test reservations and unused prefetch are included. This is an exact counter invariant for formal arithmetic execution. It is not CPU time, heap allocation, machine-code constant space, RNG bit complexity, or a claim that existing parsing/hash/norm/Aux work vanishes.

### finalMachine_perfect_completeness

Requires s*m*n=R*W and ConditionalFull, plus explicit original Aux acceptance and zero mvResidual for the actual output's candidate. It proves acceptance for every supplied threshold and every index function. It does not assert that an unspecified signing algorithm always produces inputs meeting these validity premises. The total-work theorem's terminal reservation-room hypothesis is not needed for this completeness statement.

### Trace/state representation

finalMachine_refines proves whole-record equality with erasure of the instrumented completed machine. The final result retains current/future banks, active prepared matrix and updated pending buffer; the old pending copy, depth lists and check traces are absent. fieldSlots_card counts 2*s*n+2*s*m field coordinates in those four field families. Retaining A adds n*m coordinates. Caller-owned H/input, the external adversary program, random-tape specification, execution stack, closures/heap representations, and arbitrary-size scalar counter storage are excluded. This is a formal coordinate inventory, not a verified concrete-runtime total-memory bound.

## Actual prime field and certified arithmetic

PrimeDivisorBlocks0..7 use ordinary kernel `decide` to establish all relevant nondivisibility blocks. PrimeCertificate combines those with the square-root primality criterion to prove Nat.Prime 1073741789. CertifiedField defines ParameterField=ZMod 1073741789 and supplies the proven prime Fact needed for its Field instance, as well as Fintype and exact cardinality.

CertifiedParameters establishes the actual field margin at R=262144,k=128,s=64, ratio rho=1/2 for u=33, delta<2^-286 and E*delta<2^-222 under E≤2^64. These arithmetic dimensions do not certify 128-bit security for a particular signature scheme or instantiate SIS/GPV hardness.

## Documentation and interpretation

README-v2.md and STATUS.md accurately distinguish the finite verifier/compiler result from source-signature hardness, live resumable/forkable sessions, faults/rollback, field-operation timing leakage, ideal-to-bit-level sampling, CPU benchmarks, and novelty. Their phrase that the independent V2 rebuild is pending describes their frozen pre-audit status; this report supplies the subsequent independent evidence without modifying that frozen input.

EpochResourceBounds counts ideal bank reads and the s*n sample refresh burst. Random-bank generation remains undeamortized; no end-to-end latency bound follows from field-operation smoothing. OperationalEarlyTradeoff connects initialized actual counters to the narrow N≥R, average-depth≤6 advantage over seven terminal rows. MatchedEarlyCertificates proves arithmetic for an equal-field-storage RS row ceiling and first six threshold pairs; the RS coding-theory premise itself is not proved here, nor is there a universal lower bound or all-resource dominance theorem.

The report verifies compilation, source integrity, theorem trust and the stated endpoint assumptions. It does not establish novelty or independently validate a deployed implementation.

Important epoch-budget detail: the security endpoint uses the maximum modeled list length `phases.length+1`, not the realized selected/entered epoch count. Applying the numeric E≤2^64 certificate requires bounding this maximum list length by 2^64 (or another separately proved stopping-sensitive reduction). A resource bound on the realized number of promotions alone is not automatically a replacement in the displayed probability theorem.

Manifest control-file hashes:

- modules-v2.txt: 77fe030c91956047cf18c705a5d092ec9ab4c7a2badb1005950ae555cc7f8091
- build-all-v2.sh: 47e7989c3a2697bbf1f59d7607abc17591e798d4af9ed3db5e15e8ea6642c9a3
- check.sh: 9d3425b0fc7a79fbe438c39178341b55fbfc25cd203ad379a26a90f79e5996f3
- README-v2.md: d43da57021ad52ac0a6b659ca23bd2dbae962d6d7068d40a35d5cbe2294604ef
- STATUS.md: b0f46e59a9bdce243dae1eff3f82e120798f248a5bf1c77aeaac8029be892228

## Measured result

- Manifest compiles: 67/67 exit 0; cumulative measured module compiler time 143.297 seconds.
- Peak sampled module RSS: 1,639,044 KiB (1.563 GiB), module StoredBufferedExecution.
- Exhaustive all-module theorem audit: 862 declarations, exit 0; 25.662 seconds, peak 1,624,740 KiB.
- Whole runner wall time including audit, lock waits and overhead: 169.002 seconds.
- No resource limit triggered; no hash mismatch; no forbidden trust token or nonstandard theorem axiom found.
- Compiler warnings are retained. They include unused-variable/style lint and norm_num exponent-threshold notices; all affected modules still elaborated successfully and their theorem dependencies passed the independent audit.

`build.log`, `results.json`, `module-metrics.tsv` and all per-module logs preserve the exit/time/RSS evidence. `logs/AuditAxioms.log` preserves the full 862-declaration axiom listing. `AUDIT-SHA256SUMS` authenticates the source-only reproducibility archive's files (excluding itself).
