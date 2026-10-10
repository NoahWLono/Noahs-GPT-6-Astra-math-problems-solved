import StoppingEpochExecution

/-!
# Trace-free stored execution

These runners recurse independently of the instrumented runners. Their runtime
result types contain neither Boolean trace lists nor invocation-depth lists.
Erasure is used only in refinement statements, never in the runner definitions.
Equality preserves every retained field, including entire preparation cursors.
-/
namespace ProgressivePool.TraceErasure
open StoredCheckExecution IndexedPreparation MultiEpochExecution EpochComposition
variable {F H Y : Type*} [Field F] [DecidableEq F]
variable {s m n R r : ℕ}

structure CheckResult (Y : Type*) where
  output : Y
  checks : ℕ
  multiplications : ℕ
  additions : ℕ
  subtractions : ℕ

def eraseCheck (e : Execution Y) : CheckResult Y :=
  ⟨e.output, e.trace.length, e.multiplications, e.additions, e.subtractions⟩

def checkRun (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F) :
    QueryTree (Fin s) (Input F m n) Y → CheckResult Y
  | .leaf y => ⟨y, 0, 0, 0, 0⟩
  | .query j input next =>
      let checked := evalStored Z C j input
      let rest := checkRun Z C (next (decide (checked.value = 0)))
      ⟨rest.output, rest.checks + 1, checked.multiplications + rest.multiplications,
        checked.additions + rest.additions, checked.subtractions + rest.subtractions⟩

/-- Unconditional erasure, even for an incorrectly prepared input matrix. -/
theorem checkRun_refines (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (tree : QueryTree (Fin s) (Input F m n) Y) :
    checkRun Z C tree = eraseCheck (storedRun Z C tree) := by
  induction tree with
  | leaf y => rfl
  | query j input next ih => simp only [checkRun, storedRun, ih, eraseCheck, List.length_cons]

structure BufferedResult (F : Type*) (s m : ℕ) (Y : Type*) where
  output : Y
  checks : ℕ
  pending : CursorState F s m
  multiplications : ℕ
  additions : ℕ
  subtractions : ℕ
  reservations : ℕ

def eraseBuffered (e : StoredBufferedExecution.Result F s m Y) : BufferedResult F s m Y :=
  ⟨e.output, e.trace.length, e.pending, e.multiplications, e.additions,
    e.subtractions, e.reservations⟩

noncomputable def bufferedRun (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ) :
    {r : ℕ} → InvocationProgram (Fin s) (Input F m n) H Y r →
      CursorState F s m → BufferedResult F s m Y
  | _, .stop y, pending => ⟨y, 0, pending, 0, 0, 0, 0⟩
  | _, .invoke batch next, pending =>
      let pending' := runCursor A future W pending
      let checked := checkRun Z current batch
      let rest := bufferedRun A Z current future W (next checked.output) pending'
      ⟨rest.output, checked.checks + rest.checks, rest.pending,
        checked.multiplications + rest.multiplications,
        checked.additions + rest.additions, checked.subtractions + rest.subtractions,
        1 + rest.reservations⟩

theorem bufferedRun_refines (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ)
    {r : ℕ} (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : CursorState F s m) :
    bufferedRun A Z current future W p pending =
      eraseBuffered (StoredBufferedExecution.storedBufferedRun A Z current future W p pending) := by
  induction p generalizing pending with
  | stop y => rfl
  | invoke batch next ih =>
      simp only [bufferedRun, StoredBufferedExecution.storedBufferedRun,
        checkRun_refines, eraseCheck, ih, eraseBuffered, List.length_append]

structure Result (F H : Type*) (s n m : ℕ) where
  output : H
  current : Bank F s n
  future : Bank F s n
  prepared : Prepared F s m
  pending : CursorState F s m
  selectedEpoch : ℕ
  localReservations : ℕ
  checks : ℕ
  reservations : ℕ
  checkingMultiplications : ℕ
  checkingAdditions : ℕ
  checkingSubtractions : ℕ
  preparationMultiplications : ℕ

def erase (e : StoppingEpochExecution.Result F H s n m) : Result F H s n m :=
  ⟨e.output, e.current, e.future, e.prepared, e.pending, e.selectedEpoch,
    e.localReservations, e.trace.length, e.reservations, e.checkingMultiplications,
    e.checkingAdditions, e.checkingSubtractions, e.preparationMultiplications⟩

def phaseResult (C future : Bank F s n) (Z : Prepared F s m)
    (e : BufferedResult F s m H) : Result F H s n m :=
  ⟨e.output, C, future, Z, e.pending, 0, e.reservations, e.checks, e.reservations,
    e.multiplications, e.additions, e.subtractions, e.pending.buffer.multiplications⟩

def prepend (e : BufferedResult F s m H) (rest : Result F H s n m) : Result F H s n m :=
  ⟨rest.output, rest.current, rest.future, rest.prepared, rest.pending,
    rest.selectedEpoch+1, rest.localReservations, e.checks + rest.checks,
    e.reservations + rest.reservations,
    e.multiplications + rest.checkingMultiplications,
    e.additions + rest.checkingAdditions, e.subtractions + rest.checkingSubtractions,
    e.pending.buffer.multiplications + rest.preparationMultiplications⟩

variable [Fintype F]
noncomputable def run (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) :
    (phases : List (Phase F H s m n R)) → H → Bank F s n → Prepared F s m →
      Samples (Bank F s n) (phases.length+1) → Result F H s n m
  | [], h, C, Z, future =>
      phaseResult C future.1 Z (bufferedRun A Z C future.1 W (terminal h) initialCursor)
  | p::ps, h, C, Z, future =>
      let e := bufferedRun A Z C future.1 W (p h) initialCursor
      if stop e.output then phaseResult C future.1 Z e
      else prepend e (run A W stop terminal ps e.output future.1
        (fun j col => e.pending.buffer.value (j,col)) future.2)

noncomputable def coldRun (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) : Result F H s n m :=
  let setup := runCursor A draws.1 (s*m*n) initialCursor
  let rest := run A W stop terminal phases h draws.1
    (fun j col => setup.buffer.value (j,col)) draws.2
  { rest with preparationMultiplications := setup.buffer.multiplications + rest.preparationMultiplications }

/-- Whole-record equality proves output, bank, prepared matrix, pending cursor,
selected stopping epoch, reservations, and all arithmetic counters unchanged. -/
theorem run_refines (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (C : Bank F s n) (Z : Prepared F s m)
    (future : Samples (Bank F s n) (phases.length+1)) :
    run A W stop terminal phases h C Z future =
      erase (StoppingEpochExecution.run A W stop terminal phases h C Z future) := by
  induction phases generalizing h C Z with
  | nil => simp only [run, StoppingEpochExecution.run, bufferedRun_refines,
      phaseResult, StoppingEpochExecution.phaseResult, eraseBuffered, erase]
  | cons p ps ih =>
      simp only [run, StoppingEpochExecution.run, bufferedRun_refines, eraseBuffered]
      split
      · rfl
      · simp only [ih, prepend, StoppingEpochExecution.prepend, erase, List.length_append]

theorem coldRun_refines (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) :
    coldRun A W stop terminal phases h draws =
      erase (StoppingEpochExecution.coldRun A W stop terminal phases h draws) := by
  simp only [coldRun, StoppingEpochExecution.coldRun, run_refines, erase]

/-- Scalar-only exact checking counts, with no list lengths in the result. -/
theorem coldRun_checking (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) :
    let e := coldRun A W stop terminal phases h draws
    e.checkingMultiplications = (m+n)*e.checks ∧
    e.checkingAdditions = (m+n)*e.checks ∧ e.checkingSubtractions = e.checks := by
  simpa only [coldRun_refines, erase] using
    StoppingEpochExecution.coldRun_checking A W stop terminal phases h draws

theorem coldRun_total_multiplications (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hr : r ≤ R) (hB : s*m*n = R*W) (h : H)
    (draws : Samples (Bank F s n) (phases.length+2)) :
    let e := coldRun A W stop terminal phases h draws
    e.preparationMultiplications + e.checkingMultiplications =
      s*m*n + e.reservations*W + (m+n)*e.checks := by
  simpa only [coldRun_refines, erase] using
    StoppingEpochExecution.coldRun_total_multiplications A W stop terminal phases hr hB h draws

/-- Cursor state equality includes the pending matrix, cursor index, decoded-task
counter and preparation multiplication counter, for partially completed phases. -/
theorem coldRun_pending (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) :
    let e := coldRun A W stop terminal phases h draws
    e.pending = runCursor A e.future (e.localReservations*W) initialCursor := by
  simpa only [coldRun_refines, erase] using
    StoppingEpochExecution.coldRun_pending A W stop terminal phases h draws

/-!
## Exact abstract field-state inventory

A stopped-run result retains two banks (`current`, `future`) and two prepared
matrices (`prepared`, `pending.buffer.value`). The sum type below indexes each
field-valued coordinate exactly once by its named component, even if values
coincide. No coordinate for the opaque client output `H` is counted. If the
read-only public matrix `A` is included, add `n*m` coordinates. A current query
input has `m+n` coordinates, supplied by the external program.

There are eleven natural-number fields in the returned state: eight top-level
counters (selected epoch, local reservations, checks, total reservations, three
checking counters, preparation multiplications), plus the pending cursor's
cursor index, decoded-task count, and buffer multiplication count. These are
unbounded naturals, so this is not a constant-bit memory claim.

This is a typed coordinate inventory, not a Lean heap/stack bound: functions,
closures, recursion continuations, external adversary program/history, output,
and the supplied future random tape are not measured. The independent runners
remove trace/depth-list construction, but no compiler allocation or CPU-time
claim is inferred from that fact. Existing cursor arithmetic is reused intact.
-/
abbrev FieldSlots (s n m : ℕ) :=
  ((Fin s × Fin n) ⊕ (Fin s × Fin n)) ⊕
    ((Fin s × Fin m) ⊕ (Fin s × Fin m))

def fieldAt (e : Result F H s n m) : FieldSlots s n m → F
  | .inl (.inl (j,i)) => e.current j i
  | .inl (.inr (j,i)) => e.future j i
  | .inr (.inl (j,col)) => e.prepared j col
  | .inr (.inr (j,col)) => e.pending.buffer.value (j,col)

theorem fieldSlots_card (s n m : ℕ) :
    Fintype.card (FieldSlots s n m) = 2*s*n + 2*s*m := by
  simp only [FieldSlots, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

abbrev PublicAndStateSlots (s n m : ℕ) := (Fin n × Fin m) ⊕ FieldSlots s n m

theorem publicAndStateSlots_card (s n m : ℕ) :
    Fintype.card (PublicAndStateSlots s n m) = n*m + 2*s*n + 2*s*m := by
  simp only [PublicAndStateSlots, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, fieldSlots_card]
  ring

#print axioms coldRun_checking
#print axioms coldRun_total_multiplications
#print axioms coldRun_pending
#print axioms fieldSlots_card
#print axioms publicAndStateSlots_card
#print axioms checkRun_refines
#print axioms bufferedRun_refines
#print axioms run_refines
#print axioms coldRun_refines
end ProgressivePool.TraceErasure
