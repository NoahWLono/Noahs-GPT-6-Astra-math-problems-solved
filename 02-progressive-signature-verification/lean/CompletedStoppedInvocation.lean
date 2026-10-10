import StoppedSignatureEndpoint
import FinalStoredInvocation

/-!
# Completing the stopped operational experiment with its reserved final call

The final candidate and threshold are fixed before the fresh index function.
Auxiliary acceptance is retained.  The last cursor advance and every requested
stored check are executed and included in the cumulative field-work counters.
-/
namespace ProgressivePool.CompletedStoppedInvocation
open Finset Classical MultiEpochExecution StoredCheckExecution EpochComposition
open IndexedPreparation OperationalSignatureEndpoint FinalStoredInvocation
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s m n R r : ℕ}

structure Result (F H : Type*) (s n m : ℕ) where
  prior : StoppingEpochExecution.Result F H s n m
  last : FinalStoredInvocation.InvocationResult F s m
  accepted : Bool
  reservations : ℕ
  checkingMultiplications : ℕ
  checkingAdditions : ℕ
  checkingSubtractions : ℕ
  preparationMultiplications : ℕ

/-- Final checking preserves Aux and consumes a reservation even at t=0.
Preparation is added by the actual difference in the pending cursor counters. -/
noncomputable def finish (A : Fin n → Fin m → F) (W : ℕ)
    (aux : H → Bool) (candidate : H → Input F m n)
    (prior : StoppingEpochExecution.Result F H s n m)
    (t : ℕ) (indices : Fin t → Fin s) : Result F H s n m :=
  let last := runFinalInvocation A prior.prepared prior.current prior.future W
    prior.localReservations prior.pending (candidate prior.output) t indices
  ⟨prior, last, aux prior.output && last.accepted, prior.reservations+1,
    prior.checkingMultiplications + last.multiplications,
    prior.checkingAdditions + last.additions,
    prior.checkingSubtractions + last.subtractions,
    prior.preparationMultiplications +
      (last.pending.buffer.multiplications - prior.pending.buffer.multiplications)⟩

noncomputable def finalMachine (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n)
    (t : ℕ) (indices : Fin t → Fin s) : Result F H s n m :=
  finish A W aux candidate
    (StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra) t indices

theorem finish_acceptance (A : Fin n → Fin m → F) (W : ℕ)
    (aux : H → Bool) (candidate : H → Input F m n)
    (prior : StoppingEpochExecution.Result F H s n m)
    (t : ℕ) (indices : Fin t → Fin s) :
    (finish A W aux candidate prior t indices).accepted = true ↔
      aux prior.output = true ∧
        ∀ i, indices i ∈ FinalStoredInvocation.zeroRows prior.prepared prior.current (candidate prior.output) := by
  simp only [finish, Bool.and_eq_true]
  rw [final_invocation_acceptance]

/-- Exact checking counters, with the final invocation included. -/
theorem finish_checking (A : Fin n → Fin m → F) (W : ℕ)
    (aux : H → Bool) (candidate : H → Input F m n)
    (prior : StoppingEpochExecution.Result F H s n m)
    (t : ℕ) (indices : Fin t → Fin s) :
    let e := finish A W aux candidate prior t indices
    e.reservations = prior.reservations+1 ∧
    e.checkingMultiplications = prior.checkingMultiplications+(m+n)*t ∧
    e.checkingAdditions = prior.checkingAdditions+(m+n)*t ∧
    e.checkingSubtractions = prior.checkingSubtractions+t := by
  have hc := final_invocation_counters A prior.prepared prior.current prior.future W
    prior.localReservations prior.pending (candidate prior.output) t indices
  dsimp only [finish]
  exact ⟨rfl, congrArg (prior.checkingMultiplications + ·) hc.2.1,
    congrArg (prior.checkingAdditions + ·) hc.2.2.1,
    congrArg (prior.checkingSubtractions + ·) hc.2.2.2⟩

/-- The final preparation counter increment is proved from cursor execution. -/
theorem finish_preparation (A : Fin n → Fin m → F) (R W : ℕ)
    (aux : H → Bool) (candidate : H → Input F m n)
    (prior : StoppingEpochExecution.Result F H s n m)
    (hcursor : prior.pending = runCursor A prior.future (prior.localReservations*W) initialCursor)
    (hcap : prior.localReservations+1 ≤ R) (hB : s*m*n = R*W)
    (t : ℕ) (indices : Fin t → Fin s) :
    (finish A W aux candidate prior t indices).preparationMultiplications =
      prior.preparationMultiplications + W := by
  have hp := final_invocation_preparation A prior.prepared prior.current prior.future R W
    prior.localReservations prior.pending hcursor hcap hB (candidate prior.output) t indices
  dsimp only [finish]
  rw [hp.2, Nat.add_sub_cancel_left]

/-- Valid original equations plus Aux pass every final fresh index, preserving
perfect completeness of the original acceptance relation. -/
theorem finish_perfect_completeness (A : Fin n → Fin m → F) (W : ℕ)
    (aux : H → Bool) (candidate : H → Input F m n)
    (prior : StoppingEpochExecution.Result F H s n m)
    (hready : Ready A prior.current prior.prepared) (haux : aux prior.output = true)
    (hvalid : mvResidual A (candidate prior.output).1 (candidate prior.output).2 = 0)
    (t : ℕ) (indices : Fin t → Fin s) :
    (finish A W aux candidate prior t indices).accepted = true := by
  apply (finish_acceptance A W aux candidate prior t indices).mpr
  refine ⟨haux, ?_⟩
  intro i
  simp only [FinalStoredInvocation.zeroRows, mem_filter, mem_univ, true_and]
  rw [stored_value_correct A _ _ hready, hvalid]
  simp [rowDot]

/-- A genuine final invocation after the stopped machine, with initialized
preparation and all final checking work included in the exact total. -/
theorem finalMachine_total_multiplications (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hr : r+1 ≤ R) (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n)
    (t : ℕ) (indices : Fin t → Fin s) :
    let prior := StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra
    let actual := finalMachine A W stop terminal phases aux candidate dummy u h draws extra t indices
    actual.preparationMultiplications + actual.checkingMultiplications =
      s*m*n + (prior.reservations+1)*W + (m+n)*(prior.trace.length+t) := by
  let packed := pack A terminal aux candidate dummy u phases draws extra
  let prior := StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra
  have hp : prior.pending = runCursor A prior.future (prior.localReservations*W) initialCursor :=
    StoppingEpochExecution.coldRun_pending A W stop terminal phases h packed
  have hcap : prior.localReservations+1 ≤ R :=
    StoppingEpochExecution.coldRun_room_for_final A W stop terminal phases hr hB hFull h packed
  have hc := StoppingEpochExecution.coldRun_total_multiplications A W stop terminal phases
    ((Nat.le_succ r).trans hr) hB h packed
  change (finish A W aux candidate prior t indices).preparationMultiplications +
    (finish A W aux candidate prior t indices).checkingMultiplications =
      s*m*n + (prior.reservations+1)*W + (m+n)*(prior.trace.length+t)
  rw [finish_preparation A R W aux candidate prior hp hcap hB,
    (finish_checking A W aux candidate prior t indices).2.1]
  change prior.preparationMultiplications + prior.checkingMultiplications =
    s*m*n + prior.reservations*W + (m+n)*prior.trace.length at hc
  calc
    _ = (prior.preparationMultiplications + prior.checkingMultiplications) + W + (m+n)*t := by omega
    _ = _ := by rw [hc]; ring

/-- Correct promoted/initial matrices give actual final perfect completeness. -/
theorem finalMachine_perfect_completeness (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n)
    (haux : aux (StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra).output = true)
    (hvalid : mvResidual A
      (candidate (StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra).output).1
      (candidate (StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra).output).2 = 0)
    (t : ℕ) (indices : Fin t → Fin s) :
    (finalMachine A W stop terminal phases aux candidate dummy u h draws extra t indices).accepted = true := by
  exact finish_perfect_completeness A W aux candidate _
    (StoppedSignatureEndpoint.machine_refines A W stop terminal phases aux candidate dummy u hB hFull h draws extra).2.2.2.2
    haux hvalid t indices

/-- Error classification is proof-only; the operational verifier preserves Aux
and does not compute a full residual in order to decide acceptance. -/
noncomputable def errorIndices (A : Fin n → Fin m → F) (W : ℕ)
    (aux : H → Bool) (candidate : H → Input F m n)
    (prior : StoppingEpochExecution.Result F H s n m) (event : Bool) (t : ℕ) :
    Finset (Fin t → Fin s) :=
  univ.filter fun indices => (finish A W aux candidate prior t indices).accepted = true ∧
    residual A candidate prior.output ≠ 0 ∧ event = true

/-- The actual final invalid-acceptance set is precisely the gated all-hit set. -/
theorem errorIndices_eq (A : Fin n → Fin m → F) (W : ℕ)
    (aux : H → Bool) (candidate : H → Input F m n)
    (prior : StoppingEpochExecution.Result F H s n m) (event : Bool) (t : ℕ) :
    errorIndices A W aux candidate prior event t =
      if (errorGate A aux candidate prior.output && event) then
        FreshSampling.allHit (FinalStoredInvocation.zeroRows prior.prepared prior.current (candidate prior.output)) t
      else ∅ := by
  ext indices
  cases event <;> by_cases ha : aux prior.output = true <;>
    by_cases hz : residual A candidate prior.output = 0 <;>
    simp [errorIndices, finish_acceptance, errorGate, ha, hz, FreshSampling.allHit, and_assoc]

/-- Explicit finite probability mass of the implemented final checker, with
independent uniform fresh indices of the preselected state-dependent length. -/
noncomputable def finalErrorMass (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (extra : Bank F s n)
    (event : Draws A terminal phases aux candidate dummy u → Bool)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) : ℚ :=
  ∑ draws, sampleWeight ((compiled A terminal phases aux candidate dummy).map
      (fun e => e.toEpoch u)).length draws *
    (((errorIndices A W aux candidate
      (StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra)
      (event draws) (T draws)).card : ℚ) /
        (univ : Finset (Fin (T draws) → Fin s)).card)

/-- Exact mass equality transfers the stopped security and joint-event bounds
to the fully executed final invocation, including Aux, residual validity and t=0. -/
theorem finalErrorMass_eq (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (extra : Bank F s n)
    (event : Draws A terminal phases aux candidate dummy u → Bool)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) :
    finalErrorMass A W stop terminal phases aux candidate dummy u h extra event T =
      StoppedSignatureEndpoint.machineErrorMass A W stop terminal phases aux candidate dummy u h extra event T := by
  rw [finalErrorMass, StoppedSignatureEndpoint.machineErrorMass, FreshSampling.acceptMass_eq]
  apply sum_congr rfl
  intro draws hd
  rw [errorIndices_eq]
  by_cases hg : (errorGate A aux candidate
      (StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra).output &&
        event draws) = true
  · simp only [hg, ite_true, FreshSampling.acceptProbability, FinalStoredInvocation.zeroRows, storedZeros]
  · simp only [hg, Bool.false_eq_true, ite_false, Finset.card_empty, Nat.cast_zero, zero_div, mul_zero, zero_mul]

#print axioms finish_checking
#print axioms finish_preparation
#print axioms finalMachine_total_multiplications
#print axioms finalMachine_perfect_completeness
#print axioms errorIndices_eq
#print axioms finalErrorMass_eq
end ProgressivePool.CompletedStoppedInvocation
