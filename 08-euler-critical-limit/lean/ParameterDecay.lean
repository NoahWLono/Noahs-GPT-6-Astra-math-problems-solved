import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Decay of the integer parameter divided by the endpoint scale

This file proves an auxiliary consequence of the positive finite scaling hypothesis
`n^3 / 2^p → lambda0`. It does not assert the endpoint-series or Euler-constant scaling limit.
No assumption about `p / n` is made.
-/

open Filter Topology

namespace EulerScaling

/-- The exact logarithmic identity for the stated finite scaling parameter. -/
theorem scaling_log_identity (n p : ℕ) (hn : 1 ≤ n) :
    Real.log (((n : ℝ) ^ 3) / (2 : ℝ) ^ p) =
      3 * Real.log (n : ℝ) - (p : ℝ) * Real.log 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
  rw [Real.log_div (pow_ne_zero 3 hn0) (pow_ne_zero p (by norm_num)),
    Real.log_pow, Real.log_pow]
  norm_num

/-- Solving the exact logarithmic identity for the quotient `p / n`. -/
theorem parameter_quotient_identity (n p : ℕ) (hn : 1 ≤ n) :
    (p : ℝ) / (n : ℝ) =
      (3 * (Real.log (n : ℝ) / (n : ℝ)) -
        Real.log (((n : ℝ) ^ 3) / (2 : ℝ) ^ p) / (n : ℝ)) / Real.log 2 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [scaling_log_identity n p hn]
  apply (eq_div_iff hlog2).2
  ring

/-- Positive finite critical scaling forces `p / n → 0` along every such pair of
natural-valued sequences. The proof uses the exact logarithmic identity, `log n / n → 0`,
and the convergence of `log (n^3 / 2^p)` divided by `n → ∞`. -/
theorem tendsto_parameter_div_scale_zero
    (n p : ℕ → ℕ) (hn_pos : ∀ ℓ, 1 ≤ n ℓ)
    (hn : Tendsto n atTop atTop) (lambda0 : ℝ) (hlambda0 : 0 < lambda0)
    (hlambda : Tendsto (fun ℓ => ((n ℓ : ℝ) ^ 3) / (2 : ℝ) ^ (p ℓ))
      atTop (𝓝 lambda0)) :
    Tendsto (fun ℓ => (p ℓ : ℝ) / (n ℓ : ℝ)) atTop (𝓝 0) := by
  have hn_real : Tendsto (fun ℓ => (n ℓ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hlog_over_id :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlogn : Tendsto (fun ℓ => Real.log (n ℓ : ℝ) / (n ℓ : ℝ))
      atTop (𝓝 0) := hlog_over_id.comp hn_real
  have hloglambda : Tendsto
      (fun ℓ => Real.log (((n ℓ : ℝ) ^ 3) / (2 : ℝ) ^ (p ℓ)) / (n ℓ : ℝ))
      atTop (𝓝 0) :=
    (hlambda.log (ne_of_gt hlambda0)).div_atTop hn_real
  have hlim := ((hlogn.const_mul 3).sub hloglambda).div_const (Real.log 2)
  simp only [mul_zero, sub_zero, zero_div] at hlim
  convert hlim using 1
  funext ℓ
  exact parameter_quotient_identity (n ℓ) (p ℓ) (hn_pos ℓ)

#check scaling_log_identity
#check parameter_quotient_identity
#check tendsto_parameter_div_scale_zero
#print axioms scaling_log_identity
#print axioms parameter_quotient_identity
#print axioms tendsto_parameter_div_scale_zero

end EulerScaling
