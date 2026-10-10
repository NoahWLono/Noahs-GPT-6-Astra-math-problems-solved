import CompletedStoppedInvocation
import RandomizedStoppedEndpoint
import CertifiedParameters
import StoppedForgerySplit

/-! Public theorem entry points for the finite operational compiler.
All setup, promotions, adaptive stopping and the reserved fresh final call are
executed by the machine whose acceptance is counted here. The ordinary source
signature hardness/security remains a separate named hypothesis. -/
namespace ProgressivePool.VerifiedCompiler
open Finset Classical MultiEpochExecution StoredCheckExecution StoredBufferedExecution
open EpochComposition IndexedPreparation OperationalSignatureEndpoint
set_option maxHeartbeats 1200000
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s n m R r : ℕ}

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
    CompletedStoppedInvocation.finalErrorMass A W stop terminal phases aux candidate dummy u h extra (fun _ => true) T ≤
      (∑ draws, sampleWeight ((compiled A terminal phases aux candidate dummy).map
        (fun e => e.toEpoch u)).length draws * (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T draws)) +
      ((phases.length+1 : ℕ) : ℚ) *
        (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u)  := by
  rw [CompletedStoppedInvocation.finalErrorMass_eq]
  exact StoppedSignatureEndpoint.operational_signature_bound A W stop terminal phases aux candidate
    dummy hdummy k u hs hu hB hFull (by omega) hc ht hfield h extra T

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
    CompletedStoppedInvocation.finalErrorMass A W stop terminal phases aux candidate dummy u h extra
      (fun draws => decide (T draws = t)) T ≤
      (((u-1 : ℕ) : ℚ)/(s : ℚ))^t *
        (∑ draws ∈ univ.filter (fun draws => T draws = t),
          sampleWeight ((compiled A terminal phases aux candidate dummy).map
            (fun e => e.toEpoch u)).length draws) +
      ((phases.length+1 : ℕ) : ℚ) *
        (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u)  := by
  rw [CompletedStoppedInvocation.finalErrorMass_eq]
  exact StoppedSignatureEndpoint.operational_signature_joint A W stop terminal phases aux candidate
    dummy hdummy k u hs hu hB hFull (by omega) hc ht hfield h extra T t

variable {C : Type*} [Fintype C]

theorem randomized_final_signature_bound
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
    (T : (c : C) → Draws A (terminal c) (phases c) aux candidate dummy u → ℕ) :
    (∑ c, weights c * CompletedStoppedInvocation.finalErrorMass A W (stop c)
      (terminal c) (phases c) aux candidate dummy u (h c) (extra c) (fun _ => true) (T c)) ≤
    (∑ c, weights c * (∑ draws, sampleWeight
      ((compiled A (terminal c) (phases c) aux candidate dummy).map (fun e => e.toEpoch u)).length draws *
        (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T c draws))) +
      (E : ℚ) * (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u)  := by
  simp_rw [CompletedStoppedInvocation.finalErrorMass_eq]
  exact RandomizedStoppedEndpoint.randomized_operational_signature_bound A W stop terminal phases
    weights hw hnorm aux candidate dummy hdummy k u E hs hu hB hFull (by omega) hE hc ht hfield h extra T

#print axioms final_signature_bound
#print axioms final_signature_joint
#print axioms randomized_final_signature_bound
end ProgressivePool.VerifiedCompiler
