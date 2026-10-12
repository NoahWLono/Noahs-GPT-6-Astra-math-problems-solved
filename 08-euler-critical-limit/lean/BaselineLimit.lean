import DenominatorLimit
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Filter Topology
open scoped BigOperators
noncomputable section
namespace EulerScalingAnalytic

/-- The classical harmonic remainder, with the value at zero unused. -/
def harmonicRemainder (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log (n : ℝ) - Real.eulerMascheroniConstant

lemma harmonicRemainder_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ harmonicRemainder n ∧ harmonicRemainder n ≤ 1 / (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlo := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have hhi := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  simp only [Real.eulerMascheroniSeq', if_neg hn0, Real.eulerMascheroniSeq] at hlo hhi
  have hlog : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    rw [← Real.log_div (by positivity) (ne_of_gt hnR)]
    have h := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / (n : ℝ))
      (div_pos (by positivity) hnR)
    calc
      Real.log (((n : ℝ) + 1) / (n : ℝ)) ≤ ((n : ℝ) + 1) / (n : ℝ) - 1 := h
      _ = 1 / (n : ℝ) := by field_simp; ring
  unfold harmonicRemainder
  constructor <;> linarith

lemma tendsto_harmonicRemainder (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun l => harmonicRemainder (n l)) atTop (𝓝 0) := by
  simpa only [harmonicRemainder, sub_self, Function.comp_def] using
    (Real.tendsto_harmonic_sub_log.comp hn).sub_const Real.eulerMascheroniConstant

lemma tendsto_parameter_mul_harmonicRemainder
    (n p : ℕ → ℕ) (hn_pos : ∀ l, 1 ≤ n l)
    (hp : Tendsto (fun l => (p l : ℝ) / (n l : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun l => (p l : ℝ) * harmonicRemainder (n l)) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro l
    exact mul_nonneg (Nat.cast_nonneg _) (harmonicRemainder_bounds (n l) (hn_pos l)).1
  · intro l
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
      (harmonicRemainder_bounds (n l) (hn_pos l)).2 (Nat.cast_nonneg (p l) : (0 : ℝ) ≤ _)
  · exact hp

lemma tendsto_parameter_mul_double_harmonicRemainder
    (n p : ℕ → ℕ) (hn_pos : ∀ l, 1 ≤ n l)
    (hp : Tendsto (fun l => (p l : ℝ) / (n l : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun l => (p l : ℝ) * harmonicRemainder (2 * n l)) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro l
    exact mul_nonneg (Nat.cast_nonneg _)
      (harmonicRemainder_bounds (2 * n l) (by have := hn_pos l; omega)).1
  · intro l
    have h := (harmonicRemainder_bounds (2 * n l) (by have := hn_pos l; omega)).2
    have hi : 1 / ((2 * n l : ℕ) : ℝ) ≤ 1 / (n l : ℝ) := by
      apply one_div_le_one_div_of_le (Nat.cast_pos.mpr (by have := hn_pos l; omega))
      exact_mod_cast (show n l ≤ 2 * n l by omega)
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (h.trans hi)
      (Nat.cast_nonneg (p l) : (0 : ℝ) ≤ _)
  · exact hp

/-- Baseline term in the exact endpoint numerator decomposition. -/
def baseline (n p : ℕ) : ℝ :=
  3 * (harmonic n : ℝ) - (p : ℝ) * ((harmonic (2 * n) : ℝ) - harmonic n)

lemma baseline_decomposition (n p : ℕ) (hn : 1 ≤ n) :
    baseline n p = 3 * Real.eulerMascheroniConstant + Real.log (scale n p) +
      3 * harmonicRemainder n + (p : ℝ) * harmonicRemainder n -
      (p : ℝ) * harmonicRemainder (2 * n) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : Real.log ((2 * n : ℕ) : ℝ) = Real.log 2 + Real.log (n : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hn0]
  rw [scale, EulerScaling.scaling_log_identity n p hn]
  unfold baseline harmonicRemainder
  rw [hlog]
  ring

theorem tendsto_baseline
    (n p : ℕ → ℕ) (hn_pos : ∀ l, 1 ≤ n l)
    (hn : Tendsto n atTop atTop) (lambda0 : ℝ) (hlambda0 : 0 < lambda0)
    (hlambda : Tendsto (fun l => scale (n l) (p l)) atTop (𝓝 lambda0)) :
    Tendsto (fun l => baseline (n l) (p l)) atTop
      (𝓝 (3 * Real.eulerMascheroniConstant + Real.log lambda0)) := by
  have hp := EulerScaling.tendsto_parameter_div_scale_zero n p hn_pos hn
    lambda0 hlambda0 hlambda
  have h := (((hlambda.log (ne_of_gt hlambda0)).const_add
    (3 * Real.eulerMascheroniConstant)).add ((tendsto_harmonicRemainder n hn).const_mul 3)).add
    (tendsto_parameter_mul_harmonicRemainder n p hn_pos hp)
  have h' := h.sub (tendsto_parameter_mul_double_harmonicRemainder n p hn_pos hp)
  simp only [mul_zero, add_zero, sub_zero] at h'
  apply h'.congr'
  exact Filter.Eventually.of_forall (fun l => (baseline_decomposition (n l) (p l) (hn_pos l)).symm)

#print axioms tendsto_baseline
end EulerScalingAnalytic
