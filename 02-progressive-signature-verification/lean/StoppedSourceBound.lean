import VerifiedCompiler

/-! The ordinary source-signature term stays an explicit assumption. These
inequalities classify finite events; they do not supply an EUF simulation or
instantiate a computational hardness assumption. -/
namespace ProgressivePool.StoppedSourceBound
open Finset Classical MultiEpochExecution StoredCheckExecution StoredBufferedExecution
open EpochComposition IndexedPreparation OperationalSignatureEndpoint
set_option maxHeartbeats 1200000
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s n m R r : ℕ}

noncomputable def ordinaryForgeryMass
    (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux fresh : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (u : ℕ) (h : H) (extra : Bank F s n) : ℚ :=
  let state := fun draws => StoppedSignatureEndpoint.machine A W stop terminal phases
    aux candidate dummy u h draws extra
  let weight := sampleWeight ((compiled A terminal phases aux candidate dummy).map
    (fun e => e.toEpoch u)).length
  FiniteForgerySplit.ordinaryMass weight (fun draws => fresh (state draws).output)
    (fun draws => aux (state draws).output)
    (fun draws => decide (residual A candidate (state draws).output = 0))

noncomputable def progressiveForgeryMass
    (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux fresh : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (u : ℕ) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) : ℚ :=
  let state := fun draws => StoppedSignatureEndpoint.machine A W stop terminal phases
    aux candidate dummy u h draws extra
  let weight := sampleWeight ((compiled A terminal phases aux candidate dummy).map
    (fun e => e.toEpoch u)).length
  FiniteForgerySplit.progressiveMass weight (fun draws => fresh (state draws).output)
    (fun draws => aux (state draws).output)
    (fun draws => storedZeros (state draws).prepared (state draws).current
      (candidate (state draws).output)) T

/-- Named source-game assumption, for the particular ordinary finite event
seen along this stopped execution. `fresh` is supplied by the source game. -/
def OrdinarySourceBound
    (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux fresh : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (u : ℕ) (h : H) (extra : Bank F s n) (baseError : ℚ) : Prop :=
  ordinaryForgeryMass A W stop terminal phases aux fresh candidate dummy u h extra ≤ baseError

/-- Specializes the stopped event split to the actual completed final error
mass. No source-security claim is hidden in this classification lemma. -/
theorem stopped_forgery_split_completed
    (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux fresh : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (u : ℕ) (hs : 0 < s) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) :
    progressiveForgeryMass A W stop terminal phases aux fresh candidate dummy u h extra T ≤
      ordinaryForgeryMass A W stop terminal phases aux fresh candidate dummy u h extra +
      CompletedStoppedInvocation.finalErrorMass A W stop terminal phases aux candidate dummy u h extra
        (fun _ => true) T := by
  rw [CompletedStoppedInvocation.finalErrorMass_eq]
  exact StoppedForgerySplit.stopped_forgery_split A W stop terminal phases aux fresh candidate dummy
    u hs h extra T

/-- Generic ordinary-source plus additional verification-error bound. -/
theorem stopped_full_bound
    (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux fresh : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (u : ℕ) (hs : 0 < s) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ)
    (baseError verificationError : ℚ)
    (hbase : OrdinarySourceBound A W stop terminal phases aux fresh candidate dummy u h extra baseError)
    (hextra : CompletedStoppedInvocation.finalErrorMass A W stop terminal phases aux candidate dummy u h extra
      (fun _ => true) T ≤ verificationError) :
    progressiveForgeryMass A W stop terminal phases aux fresh candidate dummy u h extra T ≤
      baseError + verificationError :=
  (stopped_forgery_split_completed A W stop terminal phases aux fresh candidate dummy u hs h extra T).trans
    (add_le_add hbase hextra)

/-- Compiler verification error added to an explicitly assumed ordinary
source-game bound. This theorem is not itself a cryptographic reduction. -/
theorem stopped_forgery_bound
    (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux fresh : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F)
    (hdummy : dummy ≠ 0) (k u : ℕ) (hs : 0 < s) (hu : 0 < u)
    (hB : s*m*n = R*W)
    (hFull : ∀ p ∈ phases, StoppingEpochExecution.ConditionalFull A stop p) (hr : r+1 ≤ R)
    (hc : ∀ p ∈ phases, ∀ h, invocationCaps k (mapInvocationInputs A (p h)))
    (ht : ∀ h, invocationCaps k (mapInvocationInputs A (terminal h)))
    (hfield : R*k+s < Fintype.card F) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) (baseError : ℚ)
    (hbase : OrdinarySourceBound A W stop terminal phases aux fresh candidate dummy u h extra baseError) :
    progressiveForgeryMass A W stop terminal phases aux fresh candidate dummy u h extra T ≤
      baseError + ((∑ draws, sampleWeight ((compiled A terminal phases aux candidate dummy).map
        (fun e => e.toEpoch u)).length draws * (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T draws)) +
      ((phases.length+1 : ℕ) : ℚ) *
        (((R*k+s).choose u : ℚ) / ((Fintype.card F-(R*k+s) : ℕ) : ℚ)^u)) := by
  exact stopped_full_bound A W stop terminal phases aux fresh candidate dummy u hs h extra T
    baseError _ hbase (VerifiedCompiler.final_signature_bound A W stop terminal phases aux candidate
      dummy hdummy k u hs hu hB hFull hr hc ht hfield h extra T)

#print axioms stopped_forgery_split_completed
#print axioms stopped_full_bound
#print axioms stopped_forgery_bound
end ProgressivePool.StoppedSourceBound
