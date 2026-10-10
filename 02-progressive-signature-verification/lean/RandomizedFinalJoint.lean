import VerifiedCompiler

/-! Finite independent tape mixtures for the fully executed fresh final call.
The event is joint acceptance and `T = t`; its threshold probability is retained
as the actual weighted mass, rather than recovered from an aggregate bound. -/
namespace ProgressivePool.RandomizedFinalJoint
open Finset Classical MultiEpochExecution StoredCheckExecution StoredBufferedExecution
open EpochComposition IndexedPreparation OperationalSignatureEndpoint
set_option maxHeartbeats 1200000
variable {F H C : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {s n m R r : ℕ}

/-- The tape is sampled independently before the uniform banks. For each tape,
all program factories, the stopping rule, and the threshold function are fixed;
the latter may still depend on all pre-final observations. -/
theorem randomized_final_signature_joint
    (A : Fin n → Fin m → F) (W : ℕ) (stop : C → H → Bool)
    (terminal : C → Phase F H s m n r) (phases : C → List (Phase F H s m n R))
    (weights : C → ℚ) (hw : ∀ c, 0 ≤ weights c) (hnorm : ∑ c, weights c = 1)
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (hdummy : dummy ≠ 0) (k u E : ℕ) (hs : 0 < s) (hu : 0 < u)
    (hB : s*m*n = R*W)
    (hFull : ∀ c p, p ∈ phases c → StoppingEpochExecution.ConditionalFull A (stop c) p)
    (hr : r+1 ≤ R) (hE : ∀ c, (phases c).length+1 ≤ E)
    (hc : ∀ c p, p ∈ phases c → ∀ h, invocationCaps k (mapInvocationInputs A (p h)))
    (ht : ∀ c h, invocationCaps k (mapInvocationInputs A (terminal c h)))
    (hfield : R*k+s < Fintype.card F) (h : C → H) (extra : C → Bank F s n)
    (T : (c : C) → Draws A (terminal c) (phases c) aux candidate dummy u → ℕ) (t : ℕ) :
    (∑ c, weights c * CompletedStoppedInvocation.finalErrorMass A W (stop c)
      (terminal c) (phases c) aux candidate dummy u (h c) (extra c)
        (fun draws => decide (T c draws = t)) (T c)) ≤
    (((u-1 : ℕ) : ℚ)/(s : ℚ))^t *
      (∑ c, weights c * (∑ draws ∈ univ.filter (fun draws => T c draws = t),
        sampleWeight ((compiled A (terminal c) (phases c) aux candidate dummy).map
          (fun e => e.toEpoch u)).length draws)) +
      (E : ℚ) * (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u) := by
  have hb := average_pointwise_bound weights
    (fun c => CompletedStoppedInvocation.finalErrorMass A W (stop c)
      (terminal c) (phases c) aux candidate dummy u (h c) (extra c)
        (fun draws => decide (T c draws = t)) (T c))
    (fun c => (((u-1 : ℕ) : ℚ)/(s : ℚ))^t *
      (∑ draws ∈ univ.filter (fun draws => T c draws = t),
        sampleWeight ((compiled A (terminal c) (phases c) aux candidate dummy).map
          (fun e => e.toEpoch u)).length draws))
    ((E : ℚ) * (((R*k+s).choose u : ℚ) /
      ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u)) hw hnorm (fun c => by
      apply (VerifiedCompiler.final_signature_joint A W (stop c) (terminal c)
        (phases c) aux candidate dummy hdummy k u hs hu hB (hFull c) hr
        (hc c) (ht c) hfield (h c) (extra c) (T c) t).trans
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hE c))
      exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
  calc
    _ ≤ _ := hb
    _ = _ := by rw [mul_sum]; congr 1; apply sum_congr rfl; intro c hc; ring

#print axioms randomized_final_signature_joint
end ProgressivePool.RandomizedFinalJoint
