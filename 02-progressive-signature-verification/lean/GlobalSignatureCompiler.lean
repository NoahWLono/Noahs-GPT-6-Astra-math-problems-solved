import SignatureCompiler
import EpochFreshJoint

namespace ProgressivePool
open Finset Classical
set_option maxHeartbeats 800000
variable {F I H P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

structure SignatureEpoch (s : ℕ) (H F I P : Type*) where
  query : H → QueryTree (Fin s) (I → F) P
  next : H → (Fin s → I → F) → H
  invoke : H → (Fin s → I → F) → Bool

noncomputable def compileSignatureEpoch {s : ℕ} (e : SignatureEpoch s H F I P)
    (aux : P → Bool) (residual : P → I → F) (dummy : I → F) : PoolEpoch s H F I where
  query h := mapOutput (fun p => if residual p = 0 then dummy else residual p) (e.query h)
  next := e.next
  invoke h bank := e.invoke h bank && aux (runOutput bank (e.query h)) &&
    decide (residual (runOutput bank (e.query h)) ≠ 0)

theorem compiled_query_height {s : ℕ} (e : SignatureEpoch s H F I P)
    (aux : P → Bool) (residual : P → I → F) (dummy : I → F) (h : H) :
    queryHeight ((compileSignatureEpoch e aux residual dummy).query h) = queryHeight (e.query h) := by
  exact queryHeight_map _ _

theorem compiled_query_nonzero {s : ℕ} (e : SignatureEpoch s H F I P)
    (aux : P → Bool) (residual : P → I → F) (dummy : I → F) (hdummy : dummy ≠ 0)
    (h : H) (bank : Fin s → I → F) :
    runOutput bank ((compileSignatureEpoch e aux residual dummy).query h) ≠ 0 := by
  rw [compileSignatureEpoch,runOutput_map]
  split_ifs with hz
  · exact hdummy
  · exact hz

/-- On every invocation counted as an extra verification error, the proof-only
repair leaves the actual signature residual and all projected tests unchanged. -/
theorem compiled_active_residual {s : ℕ} (e : SignatureEpoch s H F I P)
    (aux : P → Bool) (residual : P → I → F) (dummy : I → F)
    (h : H) (bank : Fin s → I → F)
    (ha : (compileSignatureEpoch e aux residual dummy).invoke h bank = true) :
    runOutput bank ((compileSignatureEpoch e aux residual dummy).query h) =
      residual (runOutput bank (e.query h)) := by
  have hn : residual (runOutput bank (e.query h)) ≠ 0 := by
    simp only [compileSignatureEpoch,Bool.and_eq_true,decide_eq_true_eq] at ha
    exact ha.2
  simp [compileSignatureEpoch,runOutput_map,hn]

noncomputable def activeAt {s : ℕ} (u : ℕ) :
    (epochs : List (PoolEpoch s H F I)) → H →
    EpochComposition.Samples (Fin s → I → F) (epochs.map (fun e => e.toEpoch u)).length →
    ℕ → Bool
  | [], _, _, _ => false
  | e :: _, h, draws, 0 => e.invoke h draws.1
  | e :: es, h, draws, n+1 => activeAt u es (e.next h draws.1) draws.2 n

/-- Gating excludes inactive and out-of-range selections even at threshold zero. -/
noncomputable def gatedEpochErrorMass {s : ℕ}
    (epochs : List (PoolEpoch s H F I)) (u : ℕ) (h : H)
    (select T : EpochComposition.Samples (Fin s → I → F)
      (epochs.map (fun e => e.toEpoch u)).length → ℕ) : ℚ :=
  FreshSampling.acceptMass univ
    (fun draws => if activeAt u epochs h draws (select draws) then
      EpochComposition.sampleWeight (epochs.map (fun e => e.toEpoch u)).length draws else 0)
    (fun draws => zeroRowsAt u epochs h draws (select draws)) T

theorem gatedEpochErrorMass_le {s : ℕ}
    (epochs : List (PoolEpoch s H F I)) (u : ℕ) (h : H)
    (select T : EpochComposition.Samples (Fin s → I → F)
      (epochs.map (fun e => e.toEpoch u)).length → ℕ) :
    gatedEpochErrorMass epochs u h select T ≤
      FreshSampling.acceptMass univ
        (EpochComposition.sampleWeight (epochs.map (fun e => e.toEpoch u)).length)
        (fun draws => zeroRowsAt u epochs h draws (select draws)) T := by
  rw [gatedEpochErrorMass,FreshSampling.acceptMass_eq,FreshSampling.acceptMass_eq]
  apply sum_le_sum
  intro draws _
  apply mul_le_mul_of_nonneg_right _ (FreshSampling.acceptProbability_nonneg _ _)
  split
  · exact le_rfl
  · exact EpochComposition.sampleWeight_nonneg _ _

/-- Global mixed-output compiler bound. Aux and residual validity are enforced by
compiled invocation gating; all final index strings are fresh after selection. -/
theorem global_signature_verification_error {s : ℕ} (hs : 0 < s)
    (source : List (SignatureEpoch s H F I P)) (aux : P → Bool)
    (residual : P → I → F) (dummy : I → F) (hdummy : dummy ≠ 0)
    (L u : ℕ) (hu : 0 < u)
    (hdepth : ∀ e ∈ source, ∀ h, queryHeight (e.query h) ≤ L)
    (hfield : L+s < Fintype.card F) (h : H)
    (select T : EpochComposition.Samples (Fin s → I → F)
      ((source.map (fun e => compileSignatureEpoch e aux residual dummy)).map
        (fun e => e.toEpoch u)).length → ℕ) :
    let epochs := source.map (fun e => compileSignatureEpoch e aux residual dummy)
    gatedEpochErrorMass epochs u h select T ≤
      (∑ draws, EpochComposition.sampleWeight (epochs.map (fun e => e.toEpoch u)).length draws *
        (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T draws)) +
      (source.length : ℚ) *
        (((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u) := by
  let epochs := source.map (fun e => compileSignatureEpoch e aux residual dummy)
  have hh : ∀ e ∈ epochs, ∀ h, queryHeight (e.query h) ≤ L := by
    intro e he h
    obtain ⟨e0,he0,rfl⟩ := List.mem_map.mp he
    rw [compiled_query_height]
    exact hdepth e0 he0 h
  have hn : ∀ e ∈ epochs, ∀ h bank, runOutput bank (e.query h) ≠ 0 := by
    intro e he h bank
    obtain ⟨e0,_,rfl⟩ := List.mem_map.mp he
    exact compiled_query_nonzero e0 aux residual dummy hdummy h bank
  have hb := (gatedEpochErrorMass_le epochs u h select T).trans
    (epochs_fresh_progressive hs epochs L u hu hh hn hfield h select T)
  simpa [epochs] using hb

#print axioms compiled_active_residual
#print axioms global_signature_verification_error
end ProgressivePool
