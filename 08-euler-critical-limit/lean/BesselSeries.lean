import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.Tannery

open Filter Topology

namespace EulerScalingAnalytic

/-- The factorial-square term; no special-function identity is assumed. -/
noncomputable def besselTerm (x : ℝ) (j : ℕ) : ℝ := x ^ j / (j.factorial : ℝ) ^ 2

lemma besselTerm_nonneg {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    0 ≤ besselTerm x j := by
  unfold besselTerm
  positivity

lemma besselTerm_le_expTerm {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    besselTerm x j ≤ x ^ j / (j.factorial : ℝ) := by
  have hf : (1 : ℝ) ≤ (j.factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos j))
  unfold besselTerm
  apply div_le_div_of_nonneg_left (pow_nonneg hx j) (by positivity)
  calc
    (j.factorial : ℝ) = (j.factorial : ℝ) * 1 := by ring
    _ ≤ (j.factorial : ℝ) * (j.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hf (le_trans zero_le_one hf)
    _ = (j.factorial : ℝ) ^ 2 := by ring

lemma summable_besselTerm {x : ℝ} (hx : 0 ≤ x) :
    Summable (besselTerm x) := by
  refine (Real.summable_pow_div_factorial x).of_norm_bounded (fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (besselTerm_nonneg hx j)]
  exact besselTerm_le_expTerm hx j

lemma besselTerm_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (j : ℕ) :
    besselTerm x j ≤ besselTerm y j := by
  unfold besselTerm
  gcongr

lemma tendsto_besselTerm {u : ℕ → ℝ} {x : ℝ}
    (h : Tendsto u atTop (𝓝 x)) (j : ℕ) :
    Tendsto (fun l => besselTerm (u l) j) atTop (𝓝 (besselTerm x j)) := by
  exact (h.pow j).div_const _

#print axioms summable_besselTerm

end EulerScalingAnalytic
