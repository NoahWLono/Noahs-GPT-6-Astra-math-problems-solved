import CriticalLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Filter Topology
open scoped BigOperators
noncomputable section
namespace EulerScalingAnalytic

lemma log_two_lower : (56 : ℝ) / 81 ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  linarith

lemma eulerMascheroni_lt_five_eighths : Real.eulerMascheroniConstant < (5 : ℝ) / 8 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 16
  have hh : (harmonic 16 : ℝ) = (2436559 : ℝ) / 720720 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 4
    norm_num at h
    exact h
  simp only [Real.eulerMascheroniSeq', show (16 : ℕ) ≠ 0 by norm_num, if_false] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [hh, hl] at h
  linarith [log_two_lower]

lemma harmonic_cast_one_le (j : ℕ) (hj : 1 ≤ j) : 1 ≤ (harmonic j : ℝ) := by
  have h := harmonic_gap_nonneg j (j - 1) (Nat.sub_le j 1)
  have hs : j - (j - 1) = 1 := by omega
  simp only [hs] at h
  norm_num [harmonic_succ] at h
  linarith

lemma harmonic_bessel_ratio_one_gt :
    (5 : ℝ) / 8 < (∑' j, (harmonic j : ℝ) * besselTerm 1 j) /
      (∑' j, besselTerm 1 j) := by
  let f : ℕ → ℝ := fun j => (harmonic j : ℝ) * besselTerm 1 j - (5 / 8) * besselTerm 1 j
  have hsH := summable_harmonic_besselTerm (x := (1 : ℝ)) (by norm_num)
  have hs0 := summable_besselTerm (x := (1 : ℝ)) (by norm_num)
  have hsf : Summable f := hsH.sub (hs0.mul_left (5 / 8))
  have htail : ∀ j ∉ Finset.range 4, 0 ≤ f j := by
    intro j hj
    have hj1 : 1 ≤ j := by simp only [Finset.mem_range] at hj; omega
    have hH := harmonic_cast_one_le j hj1
    have hb := besselTerm_nonneg (x := (1 : ℝ)) (by norm_num) j
    dsimp [f]
    nlinarith
  have hpartial : (∑ j ∈ Finset.range 4, f j) = (1 : ℝ) / 432 := by
    norm_num [f, Finset.sum_range_succ, besselTerm, harmonic_succ, Nat.factorial]
  have hsum := Summable.sum_le_tsum (Finset.range 4) htail hsf
  rw [hpartial] at hsum
  have hvalue : (∑' j, f j) = (∑' j, (harmonic j : ℝ) * besselTerm 1 j) -
      (5 / 8) * (∑' j, besselTerm 1 j) := by
    exact (hsH.tsum_sub (hs0.mul_left (5 / 8))).trans (by rw [tsum_mul_left])
  rw [hvalue] at hsum
  apply (lt_div_iff₀ (besselSeries_pos (x := (1 : ℝ)) (by norm_num))).2
  linarith

/-- The series-form critical limit at lambda = 1. -/
def criticalLimitOne : ℝ :=
  3 * Real.eulerMascheroniConstant -
    2 * (∑' j, (harmonic j : ℝ) * besselTerm 1 j) / (∑' j, besselTerm 1 j)

/-- A concrete strict bias, proved with rational finite-series bounds and no Bessel identity. -/
theorem criticalLimitOne_lt_gamma : criticalLimitOne < Real.eulerMascheroniConstant := by
  unfold criticalLimitOne
  have h1 := harmonic_bessel_ratio_one_gt
  have h2 := eulerMascheroni_lt_five_eighths
  rw [mul_div_assoc]
  linarith

lemma scale_pow_two (l : ℕ) : scale (2^l) (3*l) = 1 := by
  unfold scale
  rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_comm l 3]
  exact div_self (by positivity)

theorem tendsto_approximant_pow_two :
    Tendsto (fun l : ℕ => approximant (2^l) (3*l)) atTop (𝓝 criticalLimitOne) := by
  have hnpos : ∀ l : ℕ, 1 ≤ 2^l := fun l => Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hn : Tendsto (fun l : ℕ => 2^l) atTop atTop :=
    tendsto_atTop_mono (fun l => Nat.le_of_lt l.lt_two_pow_self) tendsto_id
  have hscale : Tendsto (fun l : ℕ => scale (2^l) (3*l)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [scale_pow_two] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  simpa only [Real.log_one, add_zero, criticalLimitOne] using
    tendsto_approximant_critical (fun l => 2^l) (fun l => 3*l) hnpos hn 1 (by norm_num) hscale

theorem not_tendsto_approximant_pow_two_gamma :
    ¬ Tendsto (fun l : ℕ => approximant (2^l) (3*l)) atTop (𝓝 Real.eulerMascheroniConstant) := by
  intro h
  have heq := tendsto_nhds_unique tendsto_approximant_pow_two h
  exact (ne_of_lt criticalLimitOne_lt_gamma) heq

#print axioms criticalLimitOne_lt_gamma
#print axioms tendsto_approximant_pow_two
#print axioms not_tendsto_approximant_pow_two_gamma
end EulerScalingAnalytic
