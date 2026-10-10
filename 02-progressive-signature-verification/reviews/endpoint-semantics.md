# Independent semantic audit: frozen V2 compiler bundle

Date: 2026-10-09.

Reviewed snapshot: `lean/SOURCE-SHA256SUMS-v2`, SHA-256 `218087b2b1b3961c6a275095e27ca46ec2d42cbb88798732c6f7ea3d7546296d`. All 72 manifest entries matched during review; `modules-v2.txt` selects 67 modules. This report is a semantic source review, not the independent clean rebuild or exhaustive theorem-axiom audit. Those checks should be reported separately.

## Verdict

**PASS for the finite, ideal-sampling, serialized compiler scope stated in `lean/README-v2.md`.**

The V1 report's substantive correspondence blockers are closed in this snapshot. The result is no longer only a probability theorem plus unrelated preparation/cost components: stored arithmetic, incremental preparation, buffer promotion, adaptive epoch stopping, the reserved final invocation, its actual acceptance event, and cumulative field-product costs are connected by refinement theorems. An independent trace-free implementation is related by whole-record equality and has direct security/completeness/resource corollaries.

This is not approval of a CPU/latency claim, total machine-memory bound, an EUF reduction, a source-signature hardness instantiation, or novelty. The explicit V2 limitations are material parts of the passing scope. No additional mathematical blocker was found within that scope.

## Prior gaps and their resolution

### Stored checks now execute and determine branches

`StoredCheckExecution.evalStored` computes the two explicit dot products from the active prepared matrix and private row. It does not compute the full public-matrix residual at runtime. `stored_value_correct` and `stored_bit_correct` identify the actual arithmetic and Boolean result with the residual-row oracle. `storedRun_output` and `storedRun_trace` lift the identity to adaptive branches and complete bit traces.

`dotLoop`, `evalStored`, and `storedRun_work` establish actual field-operation counters. The checking charge is no longer merely a stipulated d times query depth.

### Preparation, promotion, and actual stopping are connected

`IndexedPreparation` retains the earlier accumulator invariant and exact cursor/task-fold correspondence. `StoredBufferedExecution` interleaves that cursor with actual stored checking, including zero-check invocation reservations. Its preparation and boundary theorems identify the completed coefficients, not just paid credits.

`StoppingEpochExecution.run` now has the previously missing transition: on a continuing phase it activates the completed pending matrix and its corresponding future bank, resets the next cursor, and continues. On a stopping branch it retains the current bank and matrix. `run_refines` and `coldRun_refines` identify the resulting candidate, bank, selected epoch, local reservation count, and prepared-matrix correctness with the raw experiment.

`ConditionalFull` is an explicit admissible-schedule condition: continuing phases use R reservations, stopping phases leave a slot for the final call. It is not an assumed probability bound. The theorem does not claim to cover executions violating that schedule, rollback, or session forks.

### The actual final invocation is in the probability event

`FinalStoredInvocation.checkFresh` performs all t requested stored checks and ANDs the computed bits. It deliberately does not short-circuit on rejection. Its accepting-set theorem identifies exactly the all-hit index strings, and its finite uniform probability is the corresponding power of the actual stored zero-row fraction.

`runFinalInvocation` advances preparation and reserves a slot even for t=0. `CompletedStoppedInvocation.finish` preserves Aux in acceptance and includes the final preparation/checking work. `errorIndices_eq` and `finalErrorMass_eq` connect actual invalid acceptance, including Aux failure, zero residual, and threshold-zero cases, to the previously proved probability experiment.

`StoppedSignatureEndpoint.machine_mass_eq` supplies the source/operational mass equality across adaptive earlier stopping. `VerifiedCompiler` then gives aggregate and joint-threshold bounds for that completed machine. There is no residual-selection oracle or abstract bad-event assumption substituted for actual final acceptance.

### Whole-run products and completeness are now proved

The cold-run and completed-final-call identities include setup, every reached complete/partial phase, unused prefetch, zero-check calls, and the designated final reservation. For the represented run they give exactly B+NW+(m+n)S, where N includes the final call and S is the actual number of executed checks.

`CompletedStoppedInvocation.finalMachine_perfect_completeness` proves acceptance for every final index string when Aux holds and the original equation is valid, using the correctly initialized/promoted active matrix. These results transfer to `FinalTraceErasure.finalMachine`.

### Erasure is an implementation refinement, not merely a smaller type assertion

`TraceErasure` defines separate stored, buffered, and stopped runners without constructing the trace/depth lists. `FinalTraceErasure.finish` removes the old pending-buffer record as well. Its refinement theorem equates every retained component with the erased instrumented result; its probability specification explicitly reads the independent trace-free machine's acceptance.

Direct final aggregate/joint bounds, completeness, and scalar multiplication-cost theorems apply to that implementation. The field-coordinate inventory is consistent with its retained two banks and two prepared matrices. It remains an abstract inventory, with the exclusions stated in the README, rather than a heap/stack bound.

### Randomized tapes, source security, and concrete field are explicit

`VerifiedCompiler.randomized_final_signature_bound` and `RandomizedFinalJoint.randomized_final_signature_joint` average over normalized, nonnegative finite rational tape weights. The weights are outside the bank/final-index sampling experiment, expressing the necessary independence. The threshold-dependent expectation and joint threshold mass are preserved.

`StoppedSourceBound.OrdinarySourceBound` names the separate ordinary-forgery hypothesis; its theorem adds the verified additional error without asserting an EUF simulation. This is the appropriate boundary for the supplied-verifier compiler.

`PrimeCertificate` proves the concrete modulus prime; `CertifiedField` instantiates `ZMod 1073741789` as an actual field. `CertifiedParameters` proves the field margin, rho=1/2, the conservative tail bound below 2^-286, and the global numerical bound below 2^-222 under E<=2^64. The previous assumed-field concern is resolved.

## Conditions that must remain visible in claims

1. **Epoch multiplier:** E is a deterministic upper allowance, such as the maximum phase-list length plus one, not the realized number of reached epochs or its expectation. The theorems permit earlier stopping but do not automatically replace that multiplier by a smaller random count. `EpochResourceBounds` separately relates reached epochs and actual reservations.
2. **Fresh sampling and commitment:** the final residual and threshold are fixed before the fresh final index function. Arbitrary dependence of T on the bank experiment is a stronger abstract allowance, not permission to choose T after inspecting final outcomes. The joint theorem is not a conditional rare-threshold calibration theorem.
3. **Finite model:** randomized averaging covers finite tape spaces with rational weights and the declared independence. General continuous distributions, unbounded interactions, or correlated private-bank leakage are not silently included.
4. **Admissible requests:** prior per-invocation caps and the full/stop reservation condition are hypotheses of the execution model. `VerifierInterface` clamps the final requested threshold to k and proves the confidence interface. Confidence nontriviality additionally requires 1<=u<=s and k>=1; a probability inequality valid for broader parameters does not remove those confidence requirements.
5. **Operation dimensions:** field products/additions/subtractions are modeled; decoding, control, hashing, norm/parsing/Aux work, bit-level randomness, and CPU latency remain separate. The actual final checker runs all requested checks even after a rejecting bit.
6. **Random generation:** the bank-tape access count exposes two setup banks and an sn-field-sample burst at promotion. It is not a deamortized random-generator implementation. The unused extra future bank can be fixed in the security theorem because it is never activated within the bounded experiment; the bound is uniform in that parameter.
7. **Storage:** nm+2s(n+m) is the named field-coordinate inventory, excluding external input/history/program/tape and concrete heap/stack representation. Functional updates and recursive code do not establish a compiled in-place memory bound.
8. **Security and comparison:** the checked denominator remains q−L−s. Source security is a named hypothesis. The finite comparison is initialized field-multiplication work at the specified horizons/average depths, not universal efficiency dominance, a CPU benchmark, or source-signature security parameter certification.

## Documentation and reporting recommendation

`README-v2.md` and `STATUS.md` now make these limitations substantially clear. In a short summary, say:

“Independent semantic review passed for the finite serialized private-pool compiler: actual stored checking and refreshed preparation refine the adaptive security experiment, with explicit final sampling, completeness, and initialization-inclusive field-operation counts. Sampling bursts, total memory/runtime, source-signature hardness, and novelty remain separate.”

Do not describe the enlarged bundle as independently rebuilt until the separate clean-build/axiom audit finishes. This V2 report supersedes the V1 report's open correspondence findings for this exact manifest; it does not alter or retrospectively validate the earlier snapshot.
