import ConcreteEpochs

namespace ProgressivePool
open Finset Classical
set_option maxHeartbeats 800000
variable {F I H : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

noncomputable def zeroRowsAt {s : ℕ} (u : ℕ) :
    (epochs : List (PoolEpoch s H F I)) → H →
    EpochComposition.Samples (Fin s → I → F) (epochs.map (fun e => e.toEpoch u)).length →
    ℕ → Finset (Fin s)
  | [], _, _, _ => ∅
  | e :: _, h, draws, 0 =>
      if e.invoke h draws.1 then finalZeroRows (e.query h) draws.1 else ∅
  | e :: es, h, draws, n+1 => zeroRowsAt u es (e.next h draws.1) draws.2 n

/-- The selected set comes from the residual fixed locally in its own epoch.
Future banks may select an epoch but cannot alter its residual. -/
theorem zeroRowsAt_bad {s : ℕ} (u : ℕ) (hu : 0 < u)
    (epochs : List (PoolEpoch s H F I)) (h : H)
    (draws : EpochComposition.Samples (Fin s → I → F)
      (epochs.map (fun e => e.toEpoch u)).length) (n : ℕ)
    (hbad : u ≤ (zeroRowsAt u epochs h draws n).card) :
    EpochComposition.badAt (epochs.map (fun e => e.toEpoch u)) h draws n = true := by
  induction epochs generalizing h n with
  | nil => simp [zeroRowsAt] at hbad; omega
  | cons e es ih =>
    cases n with
    | zero =>
      simp only [zeroRowsAt] at hbad
      split_ifs at hbad with hi
      · simp [EpochComposition.badAt,PoolEpoch.toEpoch,hi,hbad]
      · simp at hbad; omega
    | succ n =>
      exact ih (e.next h draws.1) draws.2 n hbad

/-- Fresh final index strings are drawn only AFTER epoch selection and threshold
selection. Their independence is encoded by acceptMass, not assumed. -/
theorem epochs_fresh_progressive {s : ℕ} (hs : 0 < s)
    (epochs : List (PoolEpoch s H F I)) (L u : ℕ) (hu : 0 < u)
    (hdepth : ∀ e ∈ epochs, ∀ h, queryHeight (e.query h) ≤ L)
    (hnonzero : ∀ e ∈ epochs, ∀ h bank, runOutput bank (e.query h) ≠ 0)
    (hfield : L+s < Fintype.card F) (h : H)
    (select T : EpochComposition.Samples (Fin s → I → F)
      (epochs.map (fun e => e.toEpoch u)).length → ℕ) :
    FreshSampling.acceptMass univ
      (EpochComposition.sampleWeight (epochs.map (fun e => e.toEpoch u)).length)
      (fun draws => zeroRowsAt u epochs h draws (select draws)) T ≤
    (∑ draws, EpochComposition.sampleWeight (epochs.map (fun e => e.toEpoch u)).length draws *
      (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T draws)) +
    (epochs.length : ℚ) *
      (((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u) := by
  let es := epochs.map (fun e => e.toEpoch u)
  let bad := fun draws => EpochComposition.badAt es h draws (select draws) = true
  have hm := FreshSampling.fresh_threshold_mixture (u := u) hs univ
    (EpochComposition.sampleWeight es.length)
    (fun draws => zeroRowsAt u epochs h draws (select draws)) T bad
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

#print axioms zeroRowsAt_bad
#print axioms epochs_fresh_progressive
end ProgressivePool
