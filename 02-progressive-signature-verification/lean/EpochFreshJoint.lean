import EpochFreshEndpoint
import FreshSamplingJoint

namespace ProgressivePool
open Finset Classical
set_option maxHeartbeats 800000
variable {F I H : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

/-- Joint event guarantee, with the actual mass of the selected threshold.
This does not assert conditional calibration on a rare threshold event. -/
theorem epochs_fresh_joint {s : ℕ} (hs : 0 < s)
    (epochs : List (PoolEpoch s H F I)) (L u : ℕ) (hu : 0 < u)
    (hdepth : ∀ e ∈ epochs, ∀ h, queryHeight (e.query h) ≤ L)
    (hnonzero : ∀ e ∈ epochs, ∀ h bank, runOutput bank (e.query h) ≠ 0)
    (hfield : L+s < Fintype.card F) (h : H)
    (select T : EpochComposition.Samples (Fin s → I → F)
      (epochs.map (fun e => e.toEpoch u)).length → ℕ) (t : ℕ) :
    FreshSampling.acceptMass univ
      (fun draws => if T draws = t then EpochComposition.sampleWeight
        (epochs.map (fun e => e.toEpoch u)).length draws else 0)
      (fun draws => zeroRowsAt u epochs h draws (select draws)) T ≤
    (((u-1 : ℕ) : ℚ)/(s : ℚ))^t *
      (∑ draws ∈ univ.filter (fun draws => T draws = t),
        EpochComposition.sampleWeight (epochs.map (fun e => e.toEpoch u)).length draws) +
    (epochs.length : ℚ) *
      (((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u) := by
  let es := epochs.map (fun e => e.toEpoch u)
  let bad := fun draws => EpochComposition.badAt es h draws (select draws) = true
  have hm := FreshSampling.fresh_joint_threshold (u := u) hs univ
    (EpochComposition.sampleWeight es.length)
    (fun draws => zeroRowsAt u epochs h draws (select draws)) T bad t
    (fun _ _ => EpochComposition.sampleWeight_nonneg _ _)
    (by
      intro draws _ hn
      have hk : ¬ u ≤ (zeroRowsAt u epochs h draws (select draws)).card := by
        intro hk
        exact hn (zeroRowsAt_bad u hu epochs h draws (select draws) hk)
      dsimp only
      omega)
  have hb : EpochComposition.sampleProbability es.length
      (fun draws => EpochComposition.badAt es h draws (select draws)) ≤
      (epochs.length : ℚ) *
        (((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u) := by
    apply le_trans _ (concrete_epochs_bad_bound epochs L u hdepth hnonzero hfield h)
    apply EpochComposition.sampleProbability_mono
    intro draws hd
    exact EpochComposition.badAt_implies_any es h draws (select draws) hd
  apply le_trans hm
  apply add_le_add
  · exact le_rfl
  · calc
      _ = EpochComposition.sampleProbability es.length
          (fun draws => EpochComposition.badAt es h draws (select draws)) := by
            simp only [EpochComposition.sampleProbability, sum_filter, bad]
            apply Finset.sum_congr
            · ext a; simp
            · intro a ha; split_ifs <;> rfl
      _ ≤ _ := hb

#print axioms epochs_fresh_joint
end ProgressivePool
