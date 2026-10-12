import DenominatorLimit
import Mathlib.NumberTheory.Harmonic.Defs

open Filter Topology
open scoped BigOperators

noncomputable section
namespace EulerScalingAnalytic

/- Harmonic-weighted series control for the critical-scaling theorem. -/

lemma besselTerm_succ_mul_sq (x : ℝ) (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) ^ 2 * besselTerm x (j + 1) = x * besselTerm x j := by
  unfold besselTerm
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ x j]
  have hj : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma summable_secondMoment_besselTerm {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun j : ℕ => (j : ℝ) ^ 2 * besselTerm x j) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [besselTerm_succ_mul_sq] using (summable_besselTerm hx).mul_left x

lemma harmonic_cast_nonneg (j : ℕ) : 0 ≤ (harmonic j : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [harmonic_succ, Rat.cast_add, Rat.cast_inv]
    exact add_nonneg ih (by positivity)

lemma harmonic_cast_le_nat (j : ℕ) : (harmonic j : ℝ) ≤ (j : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_one]
    have hi : ((j : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
    linarith

lemma harmonic_cast_le_sq (j : ℕ) : (harmonic j : ℝ) ≤ (j : ℝ) ^ 2 := by
  apply (harmonic_cast_le_nat j).trans
  cases j with
  | zero => norm_num
  | succ j =>
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    push_cast
    nlinarith

lemma summable_harmonic_besselTerm {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun j => (harmonic j : ℝ) * besselTerm x j) := by
  refine (summable_secondMoment_besselTerm hx).of_norm_bounded (fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (harmonic_cast_nonneg j) (besselTerm_nonneg hx j))]
  exact mul_le_mul_of_nonneg_right (harmonic_cast_le_sq j) (besselTerm_nonneg hx j)

theorem tendsto_harmonic_endpoint_tsum
    (n p : ℕ → ℕ) (hn_pos : ∀ l, 1 ≤ n l)
    (hn : Tendsto n atTop atTop) (lambda0 : ℝ) (hlambda0 : 0 < lambda0)
    (hlambda : Tendsto (fun l => scale (n l) (p l)) atTop (𝓝 lambda0)) :
    Tendsto (fun l => ∑' j, (harmonic j : ℝ) * endpoint (n l) (p l) j) atTop
      (𝓝 (∑' j, (harmonic j : ℝ) * besselTerm lambda0 j)) := by
  have hm : 0 ≤ lambda0 + 1 := by linarith
  have hsum := summable_harmonic_besselTerm hm
  have hbound : ∀ᶠ l in atTop, ∀ j,
      ‖(harmonic j : ℝ) * endpoint (n l) (p l) j‖ ≤
        (harmonic j : ℝ) * besselTerm (lambda0 + 1) j := by
    filter_upwards [hlambda.eventually_le_const
      (show lambda0 < lambda0 + 1 by linarith)] with l hl j
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (harmonic_cast_nonneg j) (endpoint_nonneg (n l) (p l) j))]
    exact mul_le_mul_of_nonneg_left
      ((endpoint_le_besselTerm (n l) (p l) j (hn_pos l)).trans
        (besselTerm_mono (scale_nonneg (n l) (p l)) hl j))
      (harmonic_cast_nonneg j)
  exact tendsto_tsum_of_dominated_convergence hsum
    (fun j => (tendsto_endpoint n p hn_pos hn lambda0 hlambda0 hlambda j).const_mul
      (harmonic j : ℝ)) hbound

#print axioms summable_secondMoment_besselTerm
#print axioms summable_harmonic_besselTerm
#print axioms tendsto_harmonic_endpoint_tsum

end EulerScalingAnalytic
