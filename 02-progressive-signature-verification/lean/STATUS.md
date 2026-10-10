# Progressive verification formalization status

Updated: 2026-10-09 22:15 UTC. No paper/publication artifact is authorized by this status.

## Checked scope

The original 32-module component snapshot passed an independent source-only rebuild and an exhaustive 353-theorem standard-axiom audit. Its SOURCE-SHA256SUMS remains unchanged. The enlarged operational bundle below has passed local bounded per-module Lean 4.19 checks; independent enlarged-bundle rebuild and semantic audit are still pending.

The proof starts from actual independent uniform finite-field rows and arbitrary adaptive row-index/zero-bit decision trees. It derives transcript product cells, the first-spoil conditional cardinal inequality, an adaptive finite binomial tail, and the final residual zero-row bound. No conditional-probability inequality is assumed. The checked conservative denominator is q-L-s.

New operational modules execute stored-matrix arithmetic, cursor preparation, reserve-before-response invocations, actual buffer promotion/reset, adaptive earlier epoch stopping, and a separately reserved final fresh invocation. Zero-check and aborted calls consume reservations. All actual final accepting-index sets and their finite probability masses are identified with the compiler experiment, including Aux rejection, zero residuals and threshold zero.

The main local entry points are:
- VerifiedCompiler.final_signature_bound: actual final invalid-acceptance probability <= E[rho^T] + E_epochs*delta.
- VerifiedCompiler.final_signature_joint: joint event with T=t <= rho^t Pr[T=t] + E_epochs*delta. This is not a rare-event conditional calibration claim.
- VerifiedCompiler.randomized_final_signature_bound and RandomizedFinalJoint.randomized_final_signature_joint: explicit normalized finite independent adversary/environment tape mixtures.
- CompletedStoppedInvocation.finalMachine_perfect_completeness: Aux-valid zero residuals pass every fresh index function and threshold.
- StoppedSourceBound.stopped_forgery_bound: separate named OrdinarySourceBound plus checked additional-verification error. No EUF simulation or new SIS reduction is claimed.
- CompletedStoppedInvocation.finalMachine_total_multiplications: actual initialization-inclusive B+(N+1)W+d(prior checks+t), including the designated final call.
- StoppingEpochExecution.coldRun_pending / coldRun_room_for_final: actual remaining-buffer cursor and final reservation capacity.
- VerifierInterface: clamps requests to 0..k, returns rejection or alpha at the executed threshold, and proves nontrivial monotone confidence.
- TraceErasure: independently implemented trace/depth-list-free stored and stopped runners, with whole-record erasure equality and scalar check counters. FinalTraceErasure also removes the proof-only old pending copy and retains only the updated buffer; it has direct aggregate/joint security, completeness and scalar cost corollaries.

## Parameters and comparisons

PrimeDivisorBlocks0..7 and PrimeCertificate provide kernel-checked primality of 1073741789. CertifiedField instantiates the actual ZMod field and cardinality. CertifiedParameters proves the field margin, rho=1/2, delta<2^-286 and E*delta<2^-222 for E<=2^64.

ParameterCertificate checks the preparation share, field-storage arithmetic and seven-row terminal comparator inequality. MatchedEarlyCertificates checks equal-storage RS row ceiling 1154 and the first six without-replacement threshold pairs 6,12,18,23,29,34. The RS coding-theory premise and remaining comparison values are not new compiler theorems or universal algorithmic lower bounds.

## Exact model and resource limits

- Public A is dense/unstructured. Private current and next checking banks are hidden; prior row indices and zero/nonzero outcomes may be exposed. Nonzero field values are not exposed.
- Atomic serialized invocations and precommitted final residual/threshold are covered. Live resumable/forkable final sessions, timing leakage from field arithmetic, faults and rollback are outside this model.
- A finite maximum phase list bounds total epochs. Continuing phases use R reservations. Stopping phases leave a slot for the final call. Only transition-consistent state sequences are covered.
- Field multiplication/addition/subtraction counters are exact. Cursor index decoding/control work is separate. Original hash, parsing and norm/Aux costs must be added unchanged.
- Ideal sampling draws are separate: 2sn initial field samples, sn per continuing promotion, and one fresh index per randomized check. Current bank generation is not deamortized, so the sn-sample refresh burst is explicit. No CPU-time or whole-resource dominance claim is made.
- The erasure field-slot inventory is nm+2s(n+m), plus scalar controls. It excludes caller-owned inputs, adversary state/program and random-tape specification, and is not a machine-code heap/stack bound.
- Ordinary signature security is a named hypothesis. The numerical arithmetic dimensions do not instantiate 128-bit GPV/SIS hardness or a new signature sampler.

## Review gate

No sorry, custom axioms, native_decide or trusted external numerical computation is permitted in the selected bundle. Locally printed theorem dependencies are only propext, Classical.choice and Quot.sound (or subsets). The final enlarged 67-module source manifest and independent audit must pass before calling the entire deliverable independently validated. Novelty is the narrowly reviewed combined compiler/early-confidence tradeoff; neither its probability ingredients nor progressive/randomized verification itself are claimed new.
