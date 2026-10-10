import TraceErasure
import VerifiedCompiler

/-!
# Completed trace-free verifier

The final result drops both instrumented records, including the OLD pending
buffer. It retains only the updated pending buffer, two banks and the active
prepared matrix. No trace/depth list or earlier accumulator is stored in it.
The implementation calls the trace-free cold runner and actual final arithmetic;
erasure occurs only in proofs and probability specifications.
-/
namespace ProgressivePool.FinalTraceErasure
open Finset Classical MultiEpochExecution StoredCheckExecution StoredBufferedExecution
open EpochComposition IndexedPreparation OperationalSignatureEndpoint FinalStoredInvocation
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
  checks : ℕ
  reservations : ℕ
  checkingMultiplications : ℕ
  checkingAdditions : ℕ
  checkingSubtractions : ℕ
  preparationMultiplications : ℕ
  accepted : Bool

def erase (e : CompletedStoppedInvocation.Result F H s n m) : Result F H s n m :=
  ⟨e.prior.output, e.prior.current, e.prior.future, e.prior.prepared, e.last.pending,
    e.prior.selectedEpoch, e.last.reservations, e.prior.trace.length+e.last.subtractions,
    e.reservations, e.checkingMultiplications, e.checkingAdditions,
    e.checkingSubtractions, e.preparationMultiplications, e.accepted⟩

noncomputable def finish (A : Fin n → Fin m → F) (W : ℕ)
    (aux : H → Bool) (candidate : H → Input F m n)
    (prior : TraceErasure.Result F H s n m)
    (t : ℕ) (indices : Fin t → Fin s) : Result F H s n m :=
  let last := runFinalInvocation A prior.prepared prior.current prior.future W
    prior.localReservations prior.pending (candidate prior.output) t indices
  ⟨prior.output, prior.current, prior.future, prior.prepared, last.pending,
    prior.selectedEpoch, last.reservations, prior.checks+last.subtractions,
    prior.reservations+1, prior.checkingMultiplications+last.multiplications,
    prior.checkingAdditions+last.additions, prior.checkingSubtractions+last.subtractions,
    prior.preparationMultiplications+
      (last.pending.buffer.multiplications-prior.pending.buffer.multiplications),
    aux prior.output && last.accepted⟩

theorem finish_refines (A : Fin n → Fin m → F) (W : ℕ)
    (aux : H → Bool) (candidate : H → Input F m n)
    (prior : StoppingEpochExecution.Result F H s n m)
    (t : ℕ) (indices : Fin t → Fin s) :
    finish A W aux candidate (TraceErasure.erase prior) t indices =
      erase (CompletedStoppedInvocation.finish A W aux candidate prior t indices) := rfl

noncomputable def finalMachine (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n)
    (t : ℕ) (indices : Fin t → Fin s) : Result F H s n m :=
  finish A W aux candidate
    (TraceErasure.coldRun A W stop terminal phases h
      (pack A terminal aux candidate dummy u phases draws extra)) t indices

/-- All retained state and arithmetic is equal, after dropping traces, depths,
the old cursor/buffer and the proof-only nested prior/last records. -/
theorem finalMachine_refines (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n)
    (t : ℕ) (indices : Fin t → Fin s) :
    finalMachine A W stop terminal phases aux candidate dummy u h draws extra t indices =
      erase (CompletedStoppedInvocation.finalMachine A W stop terminal phases aux candidate dummy u h draws extra t indices) := by
  simp only [finalMachine, CompletedStoppedInvocation.finalMachine,
    StoppedSignatureEndpoint.machine, TraceErasure.coldRun_refines, finish_refines]

/-- One coordinate per retained field entry; the old pending buffer is absent.
The same exclusions concerning opaque H, external program/tape and heap/stack
representation stated in TraceErasure apply. Eleven Nat controls and one Bool
are retained in addition to the four field-coordinate families. -/
def fieldAt (e : Result F H s n m) : TraceErasure.FieldSlots s n m → F
  | .inl (.inl (j,i)) => e.current j i
  | .inl (.inr (j,i)) => e.future j i
  | .inr (.inl (j,col)) => e.prepared j col
  | .inr (.inr (j,col)) => e.pending.buffer.value (j,col)

theorem fieldSlots_card (s n m : ℕ) :
    Fintype.card (TraceErasure.FieldSlots s n m) = 2*s*n+2*s*m :=
  TraceErasure.fieldSlots_card s n m

/-- Probability specification reads the actual trace-free final acceptance.
Residual classification is proof-only and is not part of finalMachine. -/
noncomputable def finalErrorMass (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (extra : Bank F s n)
    (event : Draws A terminal phases aux candidate dummy u → Bool)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) : ℚ :=
  ∑ draws, sampleWeight ((compiled A terminal phases aux candidate dummy).map
      (fun e => e.toEpoch u)).length draws *
    (((univ.filter fun indices : Fin (T draws) → Fin s =>
      let e := finalMachine A W stop terminal phases aux candidate dummy u h draws extra (T draws) indices
      e.accepted = true ∧ residual A candidate e.output ≠ 0 ∧ event draws = true).card : ℚ) /
        (univ : Finset (Fin (T draws) → Fin s)).card)

theorem finalErrorMass_eq (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (extra : Bank F s n)
    (event : Draws A terminal phases aux candidate dummy u → Bool)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) :
    finalErrorMass A W stop terminal phases aux candidate dummy u h extra event T =
      CompletedStoppedInvocation.finalErrorMass A W stop terminal phases aux candidate dummy u h extra event T := by
  simp only [finalErrorMass, CompletedStoppedInvocation.finalErrorMass,
    CompletedStoppedInvocation.errorIndices, finalMachine_refines, erase,
    CompletedStoppedInvocation.finalMachine, CompletedStoppedInvocation.finish]

theorem finalMachine_total_multiplications (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hr : r+1 ≤ R) (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n)
    (t : ℕ) (indices : Fin t → Fin s) :
    let e := finalMachine A W stop terminal phases aux candidate dummy u h draws extra t indices
    e.preparationMultiplications + e.checkingMultiplications =
      s*m*n + e.reservations*W + (m+n)*e.checks := by
  let prior := StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra
  have hl := final_invocation_counters A prior.prepared prior.current prior.future W
    prior.localReservations prior.pending (candidate prior.output) t indices
  dsimp only [prior] at hl
  have hc := CompletedStoppedInvocation.finalMachine_total_multiplications A W stop terminal phases
    aux candidate dummy u hr hB hFull h draws extra t indices
  dsimp only
  rw [finalMachine_refines]
  simpa only [erase, CompletedStoppedInvocation.finalMachine, CompletedStoppedInvocation.finish,
    hl.2.2.2] using hc

theorem finalMachine_perfect_completeness (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u) (extra : Bank F s n)
    (t : ℕ) (indices : Fin t → Fin s)
    (haux : aux (finalMachine A W stop terminal phases aux candidate dummy u h draws extra t indices).output = true)
    (hvalid : mvResidual A
      (candidate (finalMachine A W stop terminal phases aux candidate dummy u h draws extra t indices).output).1
      (candidate (finalMachine A W stop terminal phases aux candidate dummy u h draws extra t indices).output).2 = 0) :
    (finalMachine A W stop terminal phases aux candidate dummy u h draws extra t indices).accepted = true := by
  simp only [finalMachine_refines, erase, CompletedStoppedInvocation.finalMachine,
    CompletedStoppedInvocation.finish] at haux hvalid ⊢
  exact CompletedStoppedInvocation.finalMachine_perfect_completeness A W stop terminal phases
    aux candidate dummy u hB hFull h draws extra haux hvalid t indices

theorem final_signature_bound (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (hdummy : dummy ≠ 0) (k u : ℕ) (hs : 0 < s) (hu : 0 < u)
    (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p) (hr : r+1 ≤ R)
    (hc : ∀ p ∈ phases, ∀ h, invocationCaps k (mapInvocationInputs A (p h)))
    (ht : ∀ h, invocationCaps k (mapInvocationInputs A (terminal h)))
    (hfield : R*k+s < Fintype.card F) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) :
    finalErrorMass A W stop terminal phases aux candidate dummy u h extra (fun _ => true) T ≤
      (∑ draws, sampleWeight ((compiled A terminal phases aux candidate dummy).map
        (fun e => e.toEpoch u)).length draws * (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T draws)) +
      ((phases.length+1 : ℕ) : ℚ) *
        (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u)  := by
  rw [finalErrorMass_eq]
  exact VerifiedCompiler.final_signature_bound A W stop terminal phases aux candidate
    dummy hdummy k u hs hu hB hFull hr hc ht hfield h extra T

theorem final_signature_joint (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (hdummy : dummy ≠ 0) (k u : ℕ) (hs : 0 < s) (hu : 0 < u)
    (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p) (hr : r+1 ≤ R)
    (hc : ∀ p ∈ phases, ∀ h, invocationCaps k (mapInvocationInputs A (p h)))
    (ht : ∀ h, invocationCaps k (mapInvocationInputs A (terminal h)))
    (hfield : R*k+s < Fintype.card F) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) (t : ℕ) :
    finalErrorMass A W stop terminal phases aux candidate dummy u h extra
      (fun draws => decide (T draws = t)) T ≤
      (((u-1 : ℕ) : ℚ)/(s : ℚ))^t *
        (∑ draws ∈ univ.filter (fun draws => T draws = t),
          sampleWeight ((compiled A terminal phases aux candidate dummy).map
            (fun e => e.toEpoch u)).length draws) +
      ((phases.length+1 : ℕ) : ℚ) *
        (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u)  := by
  rw [finalErrorMass_eq]
  exact VerifiedCompiler.final_signature_joint A W stop terminal phases aux candidate
    dummy hdummy k u hs hu hB hFull hr hc ht hfield h extra T t

#print axioms final_signature_bound
#print axioms final_signature_joint
#print axioms finalMachine_total_multiplications
#print axioms finalMachine_perfect_completeness
#print axioms finish_refines
#print axioms finalMachine_refines
#print axioms fieldSlots_card
#print axioms finalErrorMass_eq
end ProgressivePool.FinalTraceErasure
