import StoppedSignatureEndpoint
import RandomTapeAveraging

namespace ProgressivePool.RandomizedStoppedEndpoint
open Finset Classical MultiEpochExecution StoredCheckExecution StoredBufferedExecution
open EpochComposition IndexedPreparation OperationalSignatureEndpoint
open StoppedSignatureEndpoint
set_option maxHeartbeats 1200000
variable {F H C : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {s n m R r : ℕ}

/-- A finite normalized distribution of independent adversary/environment
random tapes. Each tape fixes all program factories before uniform checking
banks are drawn. The actual threshold expectation is preserved in the bound. -/
theorem randomized_operational_signature_bound
    (A : Fin n → Fin m → F) (W : ℕ) (stop : C → H → Bool)
    (terminal : C → Phase F H s m n r) (phases : C → List (Phase F H s m n R))
    (weights : C → ℚ) (hw : ∀ c, 0 ≤ weights c) (hnorm : ∑ c, weights c = 1)
    (aux : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (hdummy : dummy ≠ 0) (k u E : ℕ) (hs : 0 < s) (hu : 0 < u)
    (hB : s*m*n = R*W)
    (hFull : ∀ c p, p ∈ phases c → StoppingEpochExecution.ConditionalFull A (stop c) p)
    (hr : r ≤ R) (hE : ∀ c, (phases c).length+1 ≤ E)
    (hc : ∀ c p, p ∈ phases c → ∀ h, invocationCaps k (mapInvocationInputs A (p h)))
    (ht : ∀ c h, invocationCaps k (mapInvocationInputs A (terminal c h)))
    (hfield : R*k+s < Fintype.card F) (h : C → H) (extra : C → Bank F s n)
    (T : (c : C) → Draws A (terminal c) (phases c) aux candidate dummy u → ℕ) :
    (∑ c, weights c * StoppedSignatureEndpoint.machineErrorMass A W (stop c)
      (terminal c) (phases c) aux candidate dummy u (h c) (extra c) (fun _ => true) (T c)) ≤
    (∑ c, weights c * (∑ draws, sampleWeight
      ((compiled A (terminal c) (phases c) aux candidate dummy).map (fun e => e.toEpoch u)).length draws *
        (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T c draws))) +
      (E : ℚ) * (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u) := by
  apply average_pointwise_bound weights _ _ _ hw hnorm
  intro c
  have hb := StoppedSignatureEndpoint.operational_signature_bound A W (stop c)
    (terminal c) (phases c) aux candidate dummy hdummy k u hs hu hB (hFull c) hr
    (hc c) (ht c) hfield (h c) (extra c) (T c)
  apply hb.trans
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hE c))
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

#print axioms randomized_operational_signature_bound
end ProgressivePool.RandomizedStoppedEndpoint
