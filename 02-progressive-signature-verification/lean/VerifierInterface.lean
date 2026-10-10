import FinalTraceErasure
import CostAndConfidence

namespace ProgressivePool.VerifierInterface
open MultiEpochExecution StoredCheckExecution OperationalSignatureEndpoint
open CompletedStoppedInvocation CostAndConfidence
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s n m R r : ℕ}

/-- The public request is clamped to the original finite progressive range. -/
def threshold (k requested : ℕ) : ℕ := min requested k

theorem threshold_le (k requested : ℕ) : threshold k requested ≤ k := Nat.min_le_right _ _

/-- Reject, or the original monotone progressive confidence at the executed
checkpoint. This wrapper performs no additional field arithmetic. -/
def response (s u t : ℕ) (accepted : Bool) : Option ℚ :=
  if accepted then some (alpha s u t) else none

noncomputable def verifyRequest (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u)
    (extra : Bank F s n) (k requested : ℕ)
    (indices : Fin (threshold k requested) → Fin s) : Option ℚ :=
  response s u (threshold k requested)
    (FinalTraceErasure.finalMachine A W stop terminal phases aux candidate dummy u h draws extra
      (threshold k requested) indices).accepted

@[simp] theorem response_isSome (s u t : ℕ) (accepted : Bool) :
    (response s u t accepted).isSome = accepted := by cases accepted <;> rfl

theorem verifyRequest_isSome (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (h : H) (draws : Draws A terminal phases aux candidate dummy u)
    (extra : Bank F s n) (k requested : ℕ)
    (indices : Fin (threshold k requested) → Fin s) :
    (verifyRequest A W stop terminal phases aux candidate dummy u h draws extra k requested indices).isSome =
      (FinalTraceErasure.finalMachine A W stop terminal phases aux candidate dummy u h draws extra
        (threshold k requested) indices).accepted := response_isSome _ _ _ _

theorem requested_confidence_monotone (hs : 0 < s) (hu : 1 ≤ u) (hus : u ≤ s) (k : ℕ) :
    Monotone (fun requested => alpha s u (threshold k requested)) := by
  intro a b hab
  exact alpha_monotone hs hu hus (min_le_min_right k hab)

theorem requested_confidence_nontrivial (hs : 0 < s) (hu : 1 ≤ u) (hus : u ≤ s)
    (k : ℕ) (hk : 1 ≤ k) :
    alpha s u (threshold k 0) = 0 ∧ 0 < alpha s u (threshold k 1) := by
  simpa [threshold,Nat.min_eq_left hk] using
    And.intro (alpha_zero s u) (alpha_one_pos hs hu hus)

#print axioms verifyRequest_isSome
#print axioms requested_confidence_monotone
#print axioms requested_confidence_nontrivial
end ProgressivePool.VerifierInterface
