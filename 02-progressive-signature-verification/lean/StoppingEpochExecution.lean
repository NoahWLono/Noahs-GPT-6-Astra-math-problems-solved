import MultiEpochCost
import OperationalSignatureEndpoint

/-!
# Adaptive early stopping across actual stored-matrix epochs

A phase may designate its output as the final candidate before the maximum
number of epochs is reached.  Stopping retains the current bank and prepared
matrix; only a continuing full phase promotes its computed next matrix.  All
work counters are from actual stored checking and cursor preparation.
-/
namespace ProgressivePool.StoppingEpochExecution
open Classical MultiEpochExecution StoredCheckExecution StoredBufferedExecution
open IndexedPreparation EpochComposition
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s m n R r : ℕ}

structure Result (F H : Type*) (s n m : ℕ) where
  output : H
  current : Bank F s n
  future : Bank F s n
  prepared : Prepared F s m
  pending : CursorState F s m
  selectedEpoch : ℕ
  localReservations : ℕ
  trace : List Bool
  reservations : ℕ
  checkingMultiplications : ℕ
  checkingAdditions : ℕ
  checkingSubtractions : ℕ
  preparationMultiplications : ℕ

noncomputable def phaseResult (C future : Bank F s n) (Z : Prepared F s m)
    (e : StoredBufferedExecution.Result F s m H) : Result F H s n m :=
  ⟨e.output, C, future, Z, e.pending, 0, e.reservations, e.trace, e.reservations,
    e.multiplications, e.additions, e.subtractions, e.pending.buffer.multiplications⟩

noncomputable def prepend (e : StoredBufferedExecution.Result F s m H)
    (rest : Result F H s n m) : Result F H s n m :=
  ⟨rest.output, rest.current, rest.future, rest.prepared, rest.pending,
    rest.selectedEpoch+1, rest.localReservations, e.trace ++ rest.trace,
    e.reservations + rest.reservations,
    e.multiplications + rest.checkingMultiplications,
    e.additions + rest.checkingAdditions, e.subtractions + rest.checkingSubtractions,
    e.pending.buffer.multiplications + rest.preparationMultiplications⟩

/-- Stop is tested on the actual stored-check output before any promotion. -/
noncomputable def run (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) :
    (phases : List (Phase F H s m n R)) → H → Bank F s n → Prepared F s m →
      Samples (Bank F s n) (phases.length+1) → Result F H s n m
  | [], h, C, Z, future =>
      phaseResult C future.1 Z (storedBufferedRun A Z C future.1 W (terminal h) initialCursor)
  | p::ps, h, C, Z, future =>
      let e := storedBufferedRun A Z C future.1 W (p h) initialCursor
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

structure RawResult (F H : Type*) (s n : ℕ) where
  output : H
  current : Bank F s n
  selectedEpoch : ℕ
  localReservations : ℕ

/-- Raw first-stop experiment.  Later banks are untouched on a stopping branch. -/
noncomputable def rawRun (A : Fin n → Fin m → F) (stop : H → Bool)
    (terminal : Phase F H s m n r) :
    (phases : List (Phase F H s m n R)) → H → Bank F s n →
      Samples (Bank F s n) (phases.length+1) → RawResult F H s n
  | [], h, C, _ =>
      ⟨runOutput C (flattenInvocations (mapInvocationInputs A (terminal h))), C, 0,
        (invocationDepths C (mapInvocationInputs A (terminal h))).length⟩
  | p::ps, h, C, future =>
      let out := runOutput C (flattenInvocations (mapInvocationInputs A (p h)))
      if stop out then ⟨out, C, 0, (invocationDepths C (mapInvocationInputs A (p h))).length⟩
      else let rest := rawRun A stop terminal ps out future.1 future.2
        { rest with selectedEpoch := rest.selectedEpoch+1 }

/-- Continue only at a full boundary.  A stopping branch leaves one reserved
slot for the fresh final invocation.  The candidate depends on the current
phase output, never on later banks. -/
def ConditionalFull (A : Fin n → Fin m → F) (stop : H → Bool)
    (p : Phase F H s m n R) : Prop :=
  ∀ h C,
    (stop (runOutput C (flattenInvocations (mapInvocationInputs A (p h)))) = false →
      (invocationDepths C (mapInvocationInputs A (p h))).length = R) ∧
    (stop (runOutput C (flattenInvocations (mapInvocationInputs A (p h)))) = true →
      (invocationDepths C (mapInvocationInputs A (p h))).length + 1 ≤ R)

lemma phase_reservations (A : Fin n → Fin m → F) (W : ℕ)
    (C future : Bank F s n) (Z : Prepared F s m) (hZ : Ready A C Z) {k : ℕ}
    (p : Program F H s m n k) :
    (storedBufferedRun A Z C future W p initialCursor).reservations =
      (invocationDepths C (mapInvocationInputs A p)).length := by
  rw [storedBuffered_reservations, storedBuffered_depths A Z C future W hZ]

/-- Operational stopping/promotion refines the raw stopped experiment exactly. -/
theorem run_refines (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, ConditionalFull A stop p)
    (h : H) (C : Bank F s n) (Z : Prepared F s m) (hZ : Ready A C Z)
    (future : Samples (Bank F s n) (phases.length+1)) :
    let actual := run A W stop terminal phases h C Z future
    let spec := rawRun A stop terminal phases h C future
    actual.output = spec.output ∧ actual.current = spec.current ∧
    actual.selectedEpoch = spec.selectedEpoch ∧ actual.localReservations = spec.localReservations ∧
      Ready A actual.current actual.prepared := by
  dsimp only
  induction phases generalizing h C Z with
  | nil =>
      exact ⟨storedBuffered_output A Z C future.1 W hZ (terminal h) initialCursor,
        rfl, rfl, phase_reservations A W C future.1 Z hZ (terminal h), hZ⟩
  | cons p ps ih =>
      let e := storedBufferedRun A Z C future.1 W (p h) initialCursor
      have ho : e.output = runOutput C (flattenInvocations (mapInvocationInputs A (p h))) :=
        storedBuffered_output A Z C future.1 W hZ (p h) initialCursor
      have hc : e.reservations = (invocationDepths C (mapInvocationInputs A (p h))).length :=
        phase_reservations A W C future.1 Z hZ (p h)
      by_cases hb : stop e.output = true
      · have hbActual : stop (storedBufferedRun A Z C future.1 W (p h) initialCursor).output = true := hb
        simp only [run, rawRun, ← ho, hbActual, hb, ite_true, phaseResult]
        exact ⟨rfl, by trivial, by trivial, hc, hZ⟩
      · have hfalse : stop (storedBufferedRun A Z C future.1 W (p h) initialCursor).output = false :=
          Bool.eq_false_iff.mpr hb
        have hraw : stop (runOutput C (flattenInvocations (mapInvocationInputs A (p h)))) = false := by
          rw [← ho]; exact hfalse
        have hR : e.reservations = R := hc.trans ((hFull p (by simp) h C).1 hraw)
        have hz' : Ready A future.1 (fun j col => e.pending.buffer.value (j,col)) :=
          (storedBuffered_boundary A Z C future.1 R W (p h) hR hB).1
        have rec := ih (fun p hp => hFull p (by simp [hp])) e.output future.1
          (fun j col => e.pending.buffer.value (j,col)) hz' future.2
        simp only [run, rawRun, ← ho, hfalse, hb, Bool.false_eq_true, ite_false, prepend]
        exact ⟨rec.1, rec.2.1, congrArg (fun x : ℕ => x+1) rec.2.2.1,
          rec.2.2.2.1, rec.2.2.2.2⟩

/-- Cold initialization is included in the same semantic refinement. -/
theorem coldRun_refines (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hB : s*m*n = R*W) (hFull : ∀ p ∈ phases, ConditionalFull A stop p)
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) :
    let actual := coldRun A W stop terminal phases h draws
    let spec := rawRun A stop terminal phases h draws.1 draws.2
    actual.output = spec.output ∧ actual.current = spec.current ∧
    actual.selectedEpoch = spec.selectedEpoch ∧ actual.localReservations = spec.localReservations ∧
      Ready A actual.current actual.prepared := by
  exact run_refines A W stop terminal phases hB hFull h draws.1 _
    (cursor_complete A draws.1).1 draws.2

/-- The first-stop index is always one of the bounded source candidates,
including the terminal fallback at index `phases.length`. -/
theorem raw_selected_le (A : Fin n → Fin m → F) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (C : Bank F s n) (future : Samples (Bank F s n) (phases.length+1)) :
    (rawRun A stop terminal phases h C future).selectedEpoch ≤ phases.length := by
  induction phases generalizing h C with
  | nil => simp [rawRun]
  | cons p ps ih =>
      simp only [rawRun]
      split
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (ih _ future.1 future.2)

/-- The selected last phase leaves the promised slot for the final invocation. -/
theorem raw_room_for_final (A : Fin n → Fin m → F) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hr : r+1 ≤ R) (hFull : ∀ p ∈ phases, ConditionalFull A stop p)
    (h : H) (C : Bank F s n) (future : Samples (Bank F s n) (phases.length+1)) :
    (rawRun A stop terminal phases h C future).localReservations + 1 ≤ R := by
  induction phases generalizing h C with
  | nil =>
      exact (Nat.succ_le_succ (invocationDepths_length_le C (mapInvocationInputs A (terminal h)))).trans hr
  | cons p ps ih =>
      simp only [rawRun]
      split
      · rename_i hb
        exact (hFull p (by simp) h C).2 hb
      · exact ih (fun p hp => hFull p (by simp [hp])) _ future.1 future.2

/-- The returned partial pending cursor is exactly the local reserved prefix. -/
theorem run_pending (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (C : Bank F s n) (Z : Prepared F s m)
    (future : Samples (Bank F s n) (phases.length+1)) :
    let e := run A W stop terminal phases h C Z future
    e.pending = runCursor A e.future (e.localReservations*W) initialCursor := by
  dsimp only
  induction phases generalizing h C Z with
  | nil =>
      simp only [run, phaseResult]
      rw [storedBuffered_preparation, storedBuffered_reservations]
  | cons p ps ih =>
      simp only [run]
      split
      · simp only [phaseResult]
        rw [storedBuffered_preparation, storedBuffered_reservations]
      · exact ih _ future.1 _ future.2

theorem coldRun_pending (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (draws : Samples (Bank F s n) (phases.length+2)) :
    let e := coldRun A W stop terminal phases h draws
    e.pending = runCursor A e.future (e.localReservations*W) initialCursor := by
  exact run_pending A W stop terminal phases h draws.1 _ draws.2

/-- Actual arithmetic remains exact under adaptive early stopping. -/
theorem run_checking (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (C : Bank F s n) (Z : Prepared F s m)
    (future : Samples (Bank F s n) (phases.length+1)) :
    let e := run A W stop terminal phases h C Z future
    e.checkingMultiplications = (m+n)*e.trace.length ∧
    e.checkingAdditions = (m+n)*e.trace.length ∧ e.checkingSubtractions = e.trace.length := by
  dsimp only
  induction phases generalizing h C Z with
  | nil => exact MultiEpochCost.phase_checking A W C future.1 Z (terminal h)
  | cons p ps ih =>
      let e := storedBufferedRun A Z C future.1 W (p h) initialCursor
      have he := MultiEpochCost.phase_checking A W C future.1 Z (p h)
      have rec := ih e.output future.1 (fun j col => e.pending.buffer.value (j,col)) future.2
      simp only [run]
      split
      · exact he
      · simp only [prepend, List.length_append]
        rw [he.1, he.2.1, he.2.2, rec.1, rec.2.1, rec.2.2, Nat.mul_add]
        exact ⟨rfl, rfl, rfl⟩

theorem run_preparation (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hr : r ≤ R) (hB : s*m*n = R*W)
    (h : H) (C : Bank F s n) (Z : Prepared F s m)
    (future : Samples (Bank F s n) (phases.length+1)) :
    (run A W stop terminal phases h C Z future).preparationMultiplications =
      (run A W stop terminal phases h C Z future).reservations * W := by
  induction phases generalizing h C Z with
  | nil => exact MultiEpochCost.phase_preparation A R W C future.1 Z (terminal h) hr hB
  | cons p ps ih =>
      let e := storedBufferedRun A Z C future.1 W (p h) initialCursor
      have he := MultiEpochCost.phase_preparation A R W C future.1 Z (p h) (le_refl R) hB
      have rec := ih e.output future.1 (fun j col => e.pending.buffer.value (j,col)) future.2
      simp only [run]
      split
      · exact he
      · simp only [prepend]
        rw [he, rec, Nat.add_mul]

theorem coldRun_checking (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R)) (h : H)
    (draws : Samples (Bank F s n) (phases.length+2)) :
    let e := coldRun A W stop terminal phases h draws
    e.checkingMultiplications = (m+n)*e.trace.length ∧
    e.checkingAdditions = (m+n)*e.trace.length ∧ e.checkingSubtractions = e.trace.length := by
  exact run_checking A W stop terminal phases h draws.1 _ draws.2

theorem coldRun_preparation (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hr : r ≤ R) (hB : s*m*n = R*W) (h : H)
    (draws : Samples (Bank F s n) (phases.length+2)) :
    (coldRun A W stop terminal phases h draws).preparationMultiplications =
      s*m*n + (coldRun A W stop terminal phases h draws).reservations*W := by
  simp only [coldRun]
  rw [(cursor_complete A draws.1).2.1, run_preparation A W stop terminal phases hr hB]

/-- Initialization-inclusive actual field work, for any adaptively stopped
prefix: B + N*W + d times the actual total checking depth. -/
theorem coldRun_total_multiplications (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hr : r ≤ R) (hB : s*m*n = R*W) (h : H)
    (draws : Samples (Bank F s n) (phases.length+2)) :
    let e := coldRun A W stop terminal phases h draws
    e.preparationMultiplications + e.checkingMultiplications =
      s*m*n + e.reservations*W + (m+n)*e.trace.length := by
  dsimp only
  rw [coldRun_preparation A W stop terminal phases hr hB,
    (coldRun_checking A W stop terminal phases h draws).1]

/-- The implemented selected phase leaves a slot for the separately reserved
final invocation, including an immediate zero-check stopping decision. -/
theorem coldRun_room_for_final (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hr : r+1 ≤ R) (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, ConditionalFull A stop p) (h : H)
    (draws : Samples (Bank F s n) (phases.length+2)) :
    (coldRun A W stop terminal phases h draws).localReservations+1 ≤ R := by
  rw [(coldRun_refines A W stop terminal phases hB hFull h draws).2.2.2.1]
  exact raw_room_for_final A stop terminal phases hr hFull h draws.1 draws.2

/-- First-stop selector, directly usable with the existing packed source draws.
The index selects a candidate already fixed by its own current-phase output. -/
noncomputable def rawSelector (A : Fin n → Fin m → F) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (C : Bank F s n) (future : Samples (Bank F s n) (phases.length+1)) : ℕ :=
  (rawRun A stop terminal phases h C future).selectedEpoch

#print axioms run_refines
#print axioms coldRun_refines
#print axioms raw_selected_le
#print axioms raw_room_for_final
#print axioms run_pending
#print axioms coldRun_pending
#print axioms coldRun_total_multiplications
#print axioms coldRun_room_for_final
end ProgressivePool.StoppingEpochExecution
