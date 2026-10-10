import GlobalSignatureCompiler

namespace ProgressivePool
open Finset Classical
set_option maxHeartbeats 800000
variable {F I H P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

noncomputable def gatedEpochJointMass {s : ℕ}
    (epochs : List (PoolEpoch s H F I)) (u : ℕ) (h : H)
    (select T : EpochComposition.Samples (Fin s → I → F)
      (epochs.map (fun e => e.toEpoch u)).length → ℕ) (t : ℕ) : ℚ :=
  FreshSampling.acceptMass univ
    (fun draws => if activeAt u epochs h draws (select draws) && decide (T draws = t) then
      EpochComposition.sampleWeight (epochs.map (fun e => e.toEpoch u)).length draws else 0)
    (fun draws => zeroRowsAt u epochs h draws (select draws)) T

theorem global_signature_joint {s : ℕ} (hs : 0 < s)
    (source : List (SignatureEpoch s H F I P)) (aux : P → Bool)
    (residual : P → I → F) (dummy : I → F) (hdummy : dummy ≠ 0)
    (L u : ℕ) (hu : 0 < u)
    (hdepth : ∀ e ∈ source, ∀ h, queryHeight (e.query h) ≤ L)
    (hfield : L+s < Fintype.card F) (h : H)
    (select T : EpochComposition.Samples (Fin s → I → F)
      ((source.map (fun e => compileSignatureEpoch e aux residual dummy)).map
        (fun e => e.toEpoch u)).length → ℕ) (t : ℕ) :
    let epochs := source.map (fun e => compileSignatureEpoch e aux residual dummy)
    gatedEpochJointMass epochs u h select T t ≤
      (((u-1 : ℕ) : ℚ)/(s : ℚ))^t *
        (∑ draws ∈ univ.filter (fun draws => T draws = t),
          EpochComposition.sampleWeight (epochs.map (fun e => e.toEpoch u)).length draws) +
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
  have hm : gatedEpochJointMass epochs u h select T t ≤
      FreshSampling.acceptMass univ
        (fun draws => if T draws = t then EpochComposition.sampleWeight
          (epochs.map (fun e => e.toEpoch u)).length draws else 0)
        (fun draws => zeroRowsAt u epochs h draws (select draws)) T := by
    rw [gatedEpochJointMass,FreshSampling.acceptMass_eq,FreshSampling.acceptMass_eq]
    apply sum_le_sum
    intro draws _
    apply mul_le_mul_of_nonneg_right _ (FreshSampling.acceptProbability_nonneg _ _)
    by_cases ht : T draws = t
    · simp only [ht,decide_true,Bool.and_true,if_true]
      split <;> simp [EpochComposition.sampleWeight_nonneg]
    · simp [ht]
  have hb := hm.trans (epochs_fresh_joint hs epochs L u hu hh hn hfield h select T t)
  simpa only [epochs,List.length_map] using hb

#print axioms global_signature_joint
end ProgressivePool
