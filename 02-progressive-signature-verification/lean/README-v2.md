# Short private-pool progressive verifier: finite proof bundle

This bundle formalizes a private preprocessing method for a supplied verifier
`Aux(candidate) AND A*sigma = target`. It does not define a new signing scheme,
instantiate source-signature hardness, or establish novelty by itself.

## Build and trust

Use the existing Lean 4.19.0/mathlib checkout in `lean-research`.
`build-all-v2.sh` builds `modules-v2.txt` in dependency order through `check.sh`.
The wrapper shares the compile lock, limits a module to 120 seconds and
2,900,000 KiB RSS, and uses one Lean worker. The v1 source manifest remains
unchanged; the v2 manifest identifies the enlarged bundle separately.

No selected source uses `sorry`, `native_decide` or a custom axiom. Standard
Lean axioms `propext`, `Classical.choice` and `Quot.sound` may occur. Primality
and arithmetic certificates are kernel checked, not trusted external output.
`STATUS.md` distinguishes local module checks from independent bundle review.

## Probability theorem

Let a checking bank have s independent uniform rows in a finite field F,
q=card(F). Prior queries may adaptively choose arbitrary row indices and
vectors and observe the zero/nonzero bit. After at most L prior row checks,
the adversary fixes a final nonzero residual. For u>0 and L+s<q:

    Pr[at least u final-zero rows]
      <= choose(L+s,u)/(q-L-s)^u = delta.

The proof derives the local conditional cardinal inequality from the actual
uniform-row experiment and transcript factorization. It does not assume the
key conditional bound. It then counts distinct row-first-spoil events and
appends virtual final tests. The sharper q-L denominator is not the checked
endpoint.

With rho=(u-1)/s and a threshold T fixed before fresh final indices, the actual
final invalid-acceptance mass is at most E[rho^T]+E_epochs*delta. The separate
joint theorem gives Pr[invalid accept AND T=t] <= rho^t Pr[T=t]+E_epochs*delta.
It does not assert a conditional guarantee after a rare threshold event.

## Operational theorem chain

- `UniformPoolEndpoint`: adaptive finite uniform-bank endpoint.
- `GlobalSignatureCompiler`, `GlobalSignatureJoint`: mixed-output epoch
  composition with Aux/nonzero gating, including inactive and T=0 cases.
- `StoredCheckExecution`: real stored-row dot products and their costs.
- `IndexedPreparation`: constant-state cursor computing the next matrix;
  task lists occur only in proof specifications.
- `StoredBufferedExecution`: every invocation reserves a slot and advances
  preparation before actual checking, including empty/aborted batches.
- `StoppingEpochExecution`: actual promotion/reset and adaptive earlier
  stopping; the next matrix is activated only after a full R-call phase.
- `StoppedSignatureEndpoint`: exact actual-machine/source-event equality.
- `CompletedStoppedInvocation`: reserved final call, unchanged Aux guard,
  actual accepting-index set, perfect completeness and cumulative costs.
- `VerifiedCompiler`: named aggregate, joint and randomized-tape final bounds.
- `RandomizedFinalJoint`: actual joint mass averaged over independent finite
  adversary/environment tapes.
- `TraceErasure`, `FinalTraceErasure`: independent implementations without
  trace/depth lists or the proof-only old pending-buffer copy; exact refinement
  and probability equality preserve the preceding results.
- `VerifierInterface`: request clamping and the rejection/confidence interface.

The probability model uses an explicit finite product of uniform bank samples.
Operational projection shows hidden prefetch does not affect the adversary's
visible history/candidate; `EpochPrefix` supplies its deferred-sampling law.
The random tape is a probability specification, not retained verifier state.

## Admissible executions

A finite maximum list bounds epochs. An adversary may stop in an earlier phase.
Every continuing phase has exactly R reserved invocations; a stopping phase
leaves one slot for the designated final call. No abort refunds a slot. Each
prior invocation has at most k row checks; the final requested threshold is
clamped to 0..k. Inputs and the final threshold are fixed before that final
invocation's fresh indices. Prior internal row bits are exposed in the proof's
stronger oracle, so restricting a real caller to atomic aggregate responses
only removes information.

The compiled source has arbitrary fixed Aux/norm/parsing predicates. All
correctness results require their original valid-input behavior. The named
`OrdinarySourceBound` in `StoppedSourceBound` is separate from the proved
additional verification error. It is not an EUF reduction.

## Resource theorem

For B=s*n*m, B=R*W, N total invocations including the designated final one, and
S total executed row checks, preparation/checking products are exactly:

    B + N*W + (m+n)*S.

Setup, each incomplete epoch, unused prefetch and zero-depth calls are included.
Each row check also performs m+n accumulator additions and one subtraction;
preparation performs one product/addition per cursor step. Cursor decoding and
control are separate integer operations. Existing hashing/norm/parsing costs
are unchanged and must be added.

`EpochResourceBounds` links reservations to the actual selected epoch and
counts ideal bank reads: two setup banks and one additional bank per promotion,
each requiring s*n independent uniform field samples. The sn-sample refresh
burst is explicit; random-bank generation is not deamortized. Each randomized
row check requires one fresh index draw. No bit-level RNG implementation or
wall-clock latency bound is claimed.

The erased state has 2sn+2sm field coordinates; including retained public A,
the field-array inventory is nm+2s(n+m). The inventory excludes caller-owned
inputs, adversary history/program, random-tape specification, execution stack
and concrete heap representation. It is not a machine-code total-memory bound.
Scalar counters and their variable-size integer representation remain explicit.

## Certified finite point and comparison boundary

q=1073741789 (proved prime), n=1024, m=61852, s=64, R=262144, k=128, u=33,
W=15463. The actual field instance has rho=1/2 and delta<2^-286; E<=2^64 yields
E*delta<2^-222. These are verifier arithmetic parameters, not certified
128-bit signature-hardness parameters.

At N>=R and average checking depth <=6, the actual initialized machine uses
strictly fewer field multiplications than N seven-row terminal checks, even
granting that comparator free setup. `OperationalEarlyTradeoff` connects this
arithmetic inequality to actual machine counters. The terminal method wins
at high confidence, cold setup and storage. The curves cross; there is no
whole-resource or universal efficiency dominance claim.

`MatchedEarlyCertificates` checks the equal-field-storage RS ceiling and first
six without-replacement threshold pairs. Reed--Solomon coding facts remain
prior mathematical baseline premises, not a newly verified general circuit
lower bound. The same random-sampling/control/norm cost dimensions must be
reported for every comparator.

## Exclusions

No live resumable/forkable final-session game, fault/rollback behavior,
value-dependent field-operation timing, source-sampler implementation, SIS
reduction, universal small-modulus efficiency result, or CPU benchmark is
asserted. Novelty assessment concerns the combined bounded-reuse compiler and
quantified early-confidence tradeoff, not its individual probability tools.
