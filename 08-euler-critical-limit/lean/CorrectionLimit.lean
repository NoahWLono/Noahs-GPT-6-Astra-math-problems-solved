import WeightedSeries
import HarmonicGap

open Filter Topology
open scoped BigOperators
noncomputable section
namespace EulerScalingAnalytic

/-- Exact residual harmonic coefficient after removing the endpoint baseline. -/
def correction (n p j : ℕ) : ℝ :=
  -((p : ℝ) + 3) * ((harmonic n : ℝ) - harmonic (n - j)) +
    (p : ℝ) * ((harmonic (2 * n) : ℝ) - harmonic (2 * n - j))

def weightedCorrection (n p j : ℕ) : ℝ := endpoint n p j * correction n p j

lemma correction_abs_le (n p j : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) :
    |correction n p j| ≤ ((p : ℝ) + 3) * (j : ℝ)^2 / (n : ℝ) := by
  have ha := harmonic_gap_bounds n j hn hj
  have hb := harmonic_gap_nonneg (2 * n) j (by omega)
  have hba := harmonic_gap_double_le n j hj
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hneg : correction n p j ≤ 0 := by unfold correction; nlinarith
  rw [abs_of_nonpos hneg]
  have hsmall : -correction n p j ≤
      ((p : ℝ) + 3) * ((harmonic n : ℝ) - harmonic (n - j)) := by
    unfold correction
    nlinarith
  calc
    -correction n p j ≤ _ := hsmall
    _ ≤ ((p : ℝ) + 3) * ((j : ℝ)^2 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left ha.2 (by positivity)
    _ = _ := by ring

lemma weightedCorrection_norm_le (n p j : ℕ) (hn : 1 ≤ n) :
    ‖weightedCorrection n p j‖ ≤ (((p : ℝ) + 3) / (n : ℝ)) *
      ((j : ℝ)^2 * besselTerm (scale n p) j) := by
  by_cases hj : j ≤ n
  · unfold weightedCorrection
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (endpoint_nonneg n p j), Real.norm_eq_abs]
    calc
      endpoint n p j * |correction n p j| ≤
          endpoint n p j * (((p : ℝ) + 3) * (j : ℝ)^2 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (correction_abs_le n p j hn hj) (endpoint_nonneg n p j)
      _ ≤ besselTerm (scale n p) j * (((p : ℝ) + 3) * (j : ℝ)^2 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (endpoint_le_besselTerm n p j hn) (by positivity)
      _ = _ := by ring
  · simp only [weightedCorrection, endpoint, if_neg hj, zero_mul, norm_zero]
    exact mul_nonneg (by positivity)
      (mul_nonneg (sq_nonneg _) (besselTerm_nonneg (scale_nonneg n p) j))

lemma tendsto_augmented_parameter_div
    (n p : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hp : Tendsto (fun l => (p l : ℝ) / (n l : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun l => ((p l : ℝ) + 3) / (n l : ℝ)) atTop (𝓝 0) := by
  have hnR : Tendsto (fun l => (n l : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have h3 : Tendsto (fun l => (3 : ℝ) / (n l : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnR
  simpa only [← add_div, add_zero] using hp.add h3

lemma tendsto_weightedCorrection
    (n p : ℕ → ℕ) (hn_pos : ∀ l, 1 ≤ n l)
    (hn : Tendsto n atTop atTop) (lambda0 : ℝ) (hlambda0 : 0 < lambda0)
    (hlambda : Tendsto (fun l => scale (n l) (p l)) atTop (𝓝 lambda0)) (j : ℕ) :
    Tendsto (fun l => weightedCorrection (n l) (p l) j) atTop (𝓝 0) := by
  have hp := EulerScaling.tendsto_parameter_div_scale_zero n p hn_pos hn
    lambda0 hlambda0 hlambda
  have ha := tendsto_augmented_parameter_div n p hn hp
  have hb := (tendsto_besselTerm hlambda j).const_mul ((j : ℝ)^2)
  have h := ha.mul hb
  simp only [zero_mul] at h
  exact squeeze_zero_norm (fun l => weightedCorrection_norm_le (n l) (p l) j (hn_pos l)) h

theorem tendsto_weightedCorrection_tsum
    (n p : ℕ → ℕ) (hn_pos : ∀ l, 1 ≤ n l)
    (hn : Tendsto n atTop atTop) (lambda0 : ℝ) (hlambda0 : 0 < lambda0)
    (hlambda : Tendsto (fun l => scale (n l) (p l)) atTop (𝓝 lambda0)) :
    Tendsto (fun l => ∑' j, weightedCorrection (n l) (p l) j) atTop (𝓝 0) := by
  have hp := EulerScaling.tendsto_parameter_div_scale_zero n p hn_pos hn
    lambda0 hlambda0 hlambda
  have ha := tendsto_augmented_parameter_div n p hn hp
  have hm : 0 ≤ lambda0 + 1 := by linarith
  have hbound : ∀ᶠ l in atTop, ∀ j,
      ‖weightedCorrection (n l) (p l) j‖ ≤ (j : ℝ)^2 * besselTerm (lambda0 + 1) j := by
    filter_upwards [hlambda.eventually_le_const (show lambda0 < lambda0 + 1 by linarith),
      ha.eventually_le_const (show (0 : ℝ) < 1 by norm_num)] with l hl hal j
    calc
      ‖weightedCorrection (n l) (p l) j‖ ≤ _ :=
        weightedCorrection_norm_le (n l) (p l) j (hn_pos l)
      _ ≤ 1 * ((j : ℝ)^2 * besselTerm (scale (n l) (p l)) j) :=
        mul_le_mul_of_nonneg_right hal
          (mul_nonneg (sq_nonneg _) (besselTerm_nonneg (scale_nonneg _ _) j))
      _ ≤ (j : ℝ)^2 * besselTerm (lambda0 + 1) j := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (besselTerm_mono (scale_nonneg _ _) hl j) (sq_nonneg _)
  have h := tendsto_tsum_of_dominated_convergence (summable_secondMoment_besselTerm hm)
    (fun j => tendsto_weightedCorrection n p hn_pos hn lambda0 hlambda0 hlambda j) hbound
  simpa only [tsum_zero] using h

#print axioms tendsto_weightedCorrection_tsum
end EulerScalingAnalytic
