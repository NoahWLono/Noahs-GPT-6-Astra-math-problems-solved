import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Bounded endpoint factors and their pointwise limit

This file proves the elementary factor estimate and its fixed-index limit.
The hypothesis `p / n → 0` is an explicit modular input, proved separately
from the positive finite critical scaling hypothesis in `ParameterDecay.lean`.
No endpoint-series or Euler-constant limit is assumed here.
-/

open Filter Topology

namespace EulerScalingAnalytic

/-- The single endpoint factor in the exact finite endpoint product. -/
noncomputable def endpointFactor (n p r : ℕ) : ℝ :=
  (1 - (r : ℝ) / (n : ℝ)) ^ 3 *
    ((1 - (r : ℝ) / (n : ℝ)) /
      (1 - (r : ℝ) / (2 * (n : ℝ)))) ^ p

private theorem unit_factor_bounds (x : ℝ) (p : ℕ)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ (1 - x) ^ 3 * ((1 - x) / (1 - x / 2)) ^ p ∧
    (1 - x) ^ 3 * ((1 - x) / (1 - x / 2)) ^ p ≤ 1 ∧
    1 - (1 - x) ^ 3 * ((1 - x) / (1 - x / 2)) ^ p ≤
      ((p : ℝ) + 3) * x := by
  have ha0 : 0 ≤ 1 - x := by linarith
  have ha1 : 1 - x ≤ 1 := by linarith
  have hd0 : 0 < 1 - x / 2 := by linarith
  have hd1 : 1 - x / 2 ≤ 1 := by linarith
  have hq0 : 0 ≤ (1 - x) / (1 - x / 2) := div_nonneg ha0 hd0.le
  have hq1 : (1 - x) / (1 - x / 2) ≤ 1 := by
    apply (div_le_one₀ hd0).2
    linarith
  have haq : 1 - x ≤ (1 - x) / (1 - x / 2) :=
    (le_div_iff₀ hd0).2 (mul_le_of_le_one_right ha0 hd1)
  have hpow0 : 0 ≤ (1 - x) ^ 3 := pow_nonneg ha0 3
  have hprod0 : 0 ≤ (1 - x) ^ 3 * ((1 - x) / (1 - x / 2)) ^ p :=
    mul_nonneg hpow0 (pow_nonneg hq0 p)
  have hprod1 : (1 - x) ^ 3 * ((1 - x) / (1 - x / 2)) ^ p ≤ 1 := by
    exact (mul_le_of_le_one_right hpow0 (pow_le_one₀ hq0 hq1)).trans
      (pow_le_one₀ ha0 ha1)
  refine ⟨hprod0, hprod1, ?_⟩
  have hcompare : (1 - x) ^ (p + 3) ≤
      (1 - x) ^ 3 * ((1 - x) / (1 - x / 2)) ^ p := by
    calc
      (1 - x) ^ (p + 3) = (1 - x) ^ 3 * (1 - x) ^ p := by
        rw [pow_add, mul_comm]
      _ ≤ (1 - x) ^ 3 * ((1 - x) / (1 - x / 2)) ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 haq p) hpow0
  have hbern := one_add_mul_sub_le_pow (by linarith : -1 ≤ 1 - x) (p + 3)
  simp only [Nat.cast_add, Nat.cast_ofNat] at hbern
  nlinarith

/-- Each factor is in `[0,1]`; its deficit is at most `(p+3) r/n`. -/
theorem endpointFactor_bounds (n p r : ℕ) (hn : 1 ≤ n) (hr : r < n) :
    0 ≤ endpointFactor n p r ∧ endpointFactor n p r ≤ 1 ∧
    0 ≤ 1 - endpointFactor n p r ∧
    1 - endpointFactor n p r ≤ ((p : ℝ) + 3) * (r : ℝ) / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hrR : (r : ℝ) < n := by exact_mod_cast hr
  have hx0 : 0 ≤ (r : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg r) hn0.le
  have hx1 : (r : ℝ) / (n : ℝ) < 1 := (div_lt_one hn0).2 hrR
  have hhalf : (r : ℝ) / (2 * (n : ℝ)) = ((r : ℝ) / (n : ℝ)) / 2 := by
    rw [div_div, mul_comm (n : ℝ) 2]
  have hb := unit_factor_bounds ((r : ℝ) / (n : ℝ)) p hx0 hx1
  unfold endpointFactor
  rw [hhalf]
  refine ⟨hb.1, hb.2.1, sub_nonneg.mpr hb.2.1, ?_⟩
  simpa only [mul_div_assoc] using hb.2.2

theorem endpointFactor_nonneg (n p r : ℕ) (hn : 1 ≤ n) (hr : r < n) :
    0 ≤ endpointFactor n p r :=
  (endpointFactor_bounds n p r hn hr).1

theorem endpointFactor_le_one (n p r : ℕ) (hn : 1 ≤ n) (hr : r < n) :
    endpointFactor n p r ≤ 1 :=
  (endpointFactor_bounds n p r hn hr).2.1

theorem endpointFactor_deficit_bounds (n p r : ℕ) (hn : 1 ≤ n) (hr : r < n) :
    0 ≤ 1 - endpointFactor n p r ∧
    1 - endpointFactor n p r ≤ ((p : ℝ) + 3) * (r : ℝ) / (n : ℝ) :=
  (endpointFactor_bounds n p r hn hr).2.2

/-- For each fixed endpoint index, the factor tends to one whenever `n → ∞`
and `p / n → 0`. -/
theorem tendsto_endpointFactor (n p : ℕ → ℕ) (hnpos : ∀ ℓ, 1 ≤ n ℓ)
    (hn : Tendsto n atTop atTop)
    (hp : Tendsto (fun ℓ => (p ℓ : ℝ) / (n ℓ : ℝ)) atTop (𝓝 0)) (r : ℕ) :
    Tendsto (fun ℓ => endpointFactor (n ℓ) (p ℓ) r) atTop (𝓝 1) := by
  have hnR : Tendsto (fun ℓ => (n ℓ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hthree : Tendsto (fun ℓ => (3 : ℝ) / (n ℓ : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnR
  have hbound : Tendsto
      (fun ℓ => ((p ℓ : ℝ) + 3) * (r : ℝ) / (n ℓ : ℝ)) atTop (𝓝 0) := by
    have h := (hp.add hthree).mul_const (r : ℝ)
    simp only [add_zero, zero_mul] at h
    convert h using 1
    funext ℓ
    ring
  have hevent : ∀ᶠ ℓ in atTop, r < n ℓ := hn.eventually (eventually_gt_atTop r)
  have hdeficit : Tendsto (fun ℓ => 1 - endpointFactor (n ℓ) (p ℓ) r)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hbound
    · filter_upwards [hevent] with ℓ hℓ
      exact (endpointFactor_deficit_bounds (n ℓ) (p ℓ) r (hnpos ℓ) hℓ).1
    · filter_upwards [hevent] with ℓ hℓ
      exact (endpointFactor_deficit_bounds (n ℓ) (p ℓ) r (hnpos ℓ) hℓ).2
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := hc.sub hdeficit
  simpa only [sub_zero, sub_sub_cancel] using h

#print axioms endpointFactor_bounds
#print axioms tendsto_endpointFactor

end EulerScalingAnalytic
