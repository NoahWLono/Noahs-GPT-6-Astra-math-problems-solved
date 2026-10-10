import StoppedSignatureEndpoint
import FiniteForgerySplit

namespace ProgressivePool.StoppedForgerySplit
open Finset Classical MultiEpochExecution StoredCheckExecution StoredBufferedExecution
open EpochComposition IndexedPreparation OperationalSignatureEndpoint
set_option maxHeartbeats 800000
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s n m R r : ℕ}

/-- Global stopped-game split. `fresh` is the ordinary game's eligibility
predicate (for example a message not queried to its signing oracle). -/
theorem stopped_forgery_split (A : Fin n → Fin m → F) (W : ℕ) (stop : H → Bool)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (aux fresh : H → Bool) (candidate : H → Input F m n) (dummy : Fin n → F) (u : ℕ)
    (hs : 0 < s) (h : H) (extra : Bank F s n)
    (T : Draws A terminal phases aux candidate dummy u → ℕ) :
    let state := fun draws => StoppedSignatureEndpoint.machine A W stop terminal phases
      aux candidate dummy u h draws extra
    let weight := sampleWeight ((compiled A terminal phases aux candidate dummy).map
      (fun e => e.toEpoch u)).length
    let fresh' := fun draws => fresh (state draws).output
    let aux' := fun draws => aux (state draws).output
    let valid := fun draws => decide (residual A candidate (state draws).output = 0)
    let K := fun draws => storedZeros (state draws).prepared (state draws).current
      (candidate (state draws).output)
    FiniteForgerySplit.progressiveMass weight fresh' aux' K T ≤
      FiniteForgerySplit.ordinaryMass weight fresh' aux' valid +
        StoppedSignatureEndpoint.machineErrorMass A W stop terminal phases aux candidate dummy u h extra
          (fun _ => true) T := by
  dsimp only
  have hh := FiniteForgerySplit.progressive_le_ordinary_add_extra hs
    (sampleWeight ((compiled A terminal phases aux candidate dummy).map (fun e => e.toEpoch u)).length)
    (sampleWeight_nonneg _) (fun draws => fresh (StoppedSignatureEndpoint.machine A W stop terminal phases
      aux candidate dummy u h draws extra).output)
    (fun draws => aux (StoppedSignatureEndpoint.machine A W stop terminal phases
      aux candidate dummy u h draws extra).output)
    (fun draws => decide (residual A candidate (StoppedSignatureEndpoint.machine A W stop terminal phases
      aux candidate dummy u h draws extra).output = 0))
    (fun draws => storedZeros (StoppedSignatureEndpoint.machine A W stop terminal phases
      aux candidate dummy u h draws extra).prepared
      (StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra).current
      (candidate (StoppedSignatureEndpoint.machine A W stop terminal phases aux candidate dummy u h draws extra).output)) T
  convert hh using 1
  congr 1
  rw [FiniteForgerySplit.extraMass,StoppedSignatureEndpoint.machineErrorMass,FreshSampling.acceptMass_eq]
  apply sum_congr rfl
  intro draws hd
  by_cases hv : residual A candidate (StoppedSignatureEndpoint.machine A W stop terminal phases
      aux candidate dummy u h draws extra).output = 0
  · simp [hv,errorGate]
  · by_cases ha : aux (StoppedSignatureEndpoint.machine A W stop terminal phases
        aux candidate dummy u h draws extra).output = true
    · simp [hv,ha,errorGate]
    · simp [hv,ha,errorGate]

#print axioms stopped_forgery_split
end ProgressivePool.StoppedForgerySplit
