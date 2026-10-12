import TaylorFourier

/-! Integer-power height estimates and a finite-product contradiction bound. -/

set_option autoImplicit false
open scoped BigOperators
open Finset Complex

namespace PillaiHeight

/-- The proposed height range supplies the actual small parameter required by Taylor. -/
theorem height_ratio_bound (m : ℕ) (hm : 6 ≤ m) (ρ A : ℝ) (hρ : 1 < ρ) (hA : 0 < A)
    (hheight : ((m : ℝ)*ρ)^m ≤ A+ρ) :
    0 < ρ/A ∧ ρ/A < 1/1000 ∧ ρ < A := by
  have hm₆ : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hrp : 0 < ρ := by linarith
  have hmexp : (46656 : ℝ) ≤ (m : ℝ)^m := by
    calc
      (46656 : ℝ) = (6 : ℝ)^6 := by norm_num
      _ ≤ (m : ℝ)^6 := by gcongr
      _ ≤ (m : ℝ)^m := by apply pow_le_pow_right₀ (by linarith) hm
  have hrpow : ρ ≤ ρ^m := by
    simpa using pow_le_pow_right₀ hρ.le (show 1 ≤ m by omega)
  have hlarge : 46656*ρ ≤ A+ρ := by
    calc
      46656*ρ ≤ (m : ℝ)^m*ρ^m := by gcongr
      _ = ((m : ℝ)*ρ)^m := (mul_pow _ _ _).symm
      _ ≤ A+ρ := hheight
  refine ⟨div_pos hrp hA,?_,?_⟩
  · apply (div_lt_iff₀ hA).mpr
    nlinarith
  · nlinarith

/-- The integer-power comparison needed for the norm product; no fractional exponents occur. -/
lemma denominator_dominates (n m : ℕ) (hn : 5 ≤ n) (hm : n < m)
    (ρ A R : ℝ) (hρ : 1 < ρ) (hA : 0 < A) (hR : 0 < R)
    (heq : R^m = A+ρ) (hRge : (m : ℝ)*ρ ≤ R) :
    ρ^2 * R^(2*n) < (m : ℝ)*A^2 := by
  have hm₆ : (6 : ℝ) ≤ m := by exact_mod_cast (show 6 ≤ m by omega)
  have hmp : (0 : ℝ) < m := by linarith
  have hrp : 0 < ρ := by linarith
  have hR₁ : 1 ≤ R := by nlinarith
  have hh : ((m : ℝ)*ρ)^m ≤ A+ρ := by rw [← heq]; gcongr
  have hρA := (height_ratio_bound m (by omega) ρ A hρ hA hh).2.2
  have hhalf : R^m < 2*A := by rw [heq]; linarith
  have hsq : R^(2*m) < 4*A^2 := by
    have h : (R^m)^2 < (2*A)^2 := by gcongr
    simpa only [← pow_mul, Nat.mul_comm m 2,mul_pow,show (2 : ℝ)^2=4 by norm_num] using h
  have hpow : R^(2*n)*R^2 ≤ R^(2*m) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hR₁ (by omega)
  have hR₂ : (m : ℝ)^2*ρ^2 ≤ R^2 := by
    simpa only [mul_pow] using (show ((m : ℝ)*ρ)^2 ≤ R^2 by gcongr)
  have hm₃ : (4 : ℝ) < (m : ℝ)^3 := by
    have h : (6 : ℝ)^3 ≤ (m : ℝ)^3 := by gcongr
    norm_num at h
    linarith
  have hmain : 4*ρ^2*R^(2*n) < 4*(m : ℝ)*A^2 := by
    calc
      4*ρ^2*R^(2*n) < (m : ℝ)^3*ρ^2*R^(2*n) := by gcongr
      _ ≤ (m : ℝ)*R^2*R^(2*n) := by
        have h := mul_le_mul_of_nonneg_left hR₂ (show 0 ≤ (m : ℝ)*R^(2*n) by positivity)
        nlinarith
      _ ≤ (m : ℝ)*R^(2*m) := by nlinarith [mul_le_mul_of_nonneg_left hpow hmp.le]
      _ < 4*(m : ℝ)*A^2 := by nlinarith [mul_lt_mul_of_pos_left hsq hmp]
  linarith

/-- A small distinguished twist and uniform bounds force the full product below one. -/
theorem product_norm_lt_one {n : ℕ} [NeZero n] (m : ℕ) (hn : 5 ≤ n) (hm : n < m)
    (ρ A R : ℝ) (hρ : 1 < ρ) (hA : 0 < A) (hR : 0 < R)
    (heq : R^m = A+ρ) (hRge : (m : ℝ)*ρ ≤ R) (β : ZMod n → ℂ)
    (hβ : ∀ i, ‖β i‖ ≤ R^2) (hβ₀ : ‖β 0‖ < ρ^2*R^2/((m : ℝ)*A^2)) :
    ‖∏ i : ZMod n, β i‖ < 1 := by
  classical
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hden : 0 < (m : ℝ)*A^2 := by positivity
  have hprod : ‖∏ i : ZMod n, β i‖ ≤ ‖β 0‖*R^(2*(n-1)) := by
    rw [norm_prod,← mul_prod_erase univ (fun i ↦ ‖β i‖) (mem_univ 0)]
    have hp : (∏ i ∈ univ.erase (0 : ZMod n), ‖β i‖) ≤
        ∏ _i ∈ univ.erase (0 : ZMod n), R^2 := by
      apply prod_le_prod (fun _ _ ↦ norm_nonneg _)
      intro i _
      exact hβ i
    have hcard : (univ.erase (0 : ZMod n)).card = n-1 := by simp
    have hp' : (∏ i ∈ univ.erase (0 : ZMod n), ‖β i‖) ≤ R^(2*(n-1)) := by
      simpa only [prod_const,hcard,← pow_mul] using hp
    exact mul_le_mul_of_nonneg_left hp' (norm_nonneg _)
  have hstrict : ‖∏ i : ZMod n, β i‖ < ρ^2*R^(2*n)/((m : ℝ)*A^2) := by
    calc
      ‖∏ i : ZMod n, β i‖ ≤ ‖β 0‖*R^(2*(n-1)) := hprod
      _ < (ρ^2*R^2/((m : ℝ)*A^2))*R^(2*(n-1)) :=
        mul_lt_mul_of_pos_right hβ₀ (pow_pos hR _)
      _ = ρ^2*R^(2*n)/((m : ℝ)*A^2) := by
        have hexp : 2+2*(n-1)=2*n := by omega
        rw [div_mul_eq_mul_div, mul_assoc (ρ^2),← pow_add,hexp]
  apply hstrict.trans
  apply (div_lt_one hden).mpr
  exact denominator_dominates n m hn hm ρ A R hρ hA hR heq hRge

lemma one_le_norm_intCast (N : ℤ) (hN : N ≠ 0) : (1 : ℝ) ≤ ‖(N : ℂ)‖ := by
  rw [Complex.norm_intCast]
  have h : (0 : ℤ) < |N| := abs_pos.mpr hN
  have h' : (1 : ℤ) ≤ |N| := by omega
  exact_mod_cast h'

end PillaiHeight
