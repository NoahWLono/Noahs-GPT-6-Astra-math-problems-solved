import PowerSamples

/-! Inverse finite Fourier transform and actual power-basis coefficient bounds. -/
set_option autoImplicit false
open scoped BigOperators
open Finset Complex
open PillaiFourier PillaiSamples
namespace PillaiCoefficients
variable {n : ℕ} [NeZero n] {ζ : ℂ}

/-- Inversion with the positive-phase, unnormalized convention. -/
theorem inverse_fourier (hζ : IsPrimitiveRoot ζ n) (a : ZMod n → ℝ) (j : ZMod n) :
    (a j : ℂ) = (n : ℂ)⁻¹ * ∑ i : ZMod n,
      gamma hζ.pow_eq_one a i * rootChar hζ.pow_eq_one (-(i*j)) := by
  classical
  have hsum : (∑ i : ZMod n, gamma hζ.pow_eq_one a i *
      rootChar hζ.pow_eq_one (-(i*j))) = (n : ℂ)*(a j : ℂ) := by
    simp only [gamma,sum_mul,mul_assoc,← AddChar.map_add_eq_mul]
    simp_rw [show ∀ i t : ZMod n, i*t+ -(i*j)=i*(t-j) by intros; ring]
    rw [sum_comm]
    simp_rw [← mul_sum,rootChar_orthogonality hζ,sub_eq_zero,mul_ite,mul_zero]
    simp [mul_comm]
  rw [hsum,← mul_assoc,inv_mul_cancel₀ (NeZero.ne (n : ℂ)),one_mul]

/-- Each coefficient is bounded by a common bound for the Fourier samples. -/
theorem coefficient_bound (hζ : IsPrimitiveRoot ζ n) (a : ZMod n → ℝ) (R : ℝ)
    (hR : ∀ i, ‖gamma hζ.pow_eq_one a i‖ ≤ R) (j : ZMod n) : |a j| ≤ R := by
  have hn : (0 : ℝ)<n := by exact_mod_cast NeZero.pos n
  calc
    |a j| = ‖(a j : ℂ)‖ := by simp
    _ = ‖(n : ℂ)⁻¹ * ∑ i : ZMod n,
        gamma hζ.pow_eq_one a i * rootChar hζ.pow_eq_one (-(i*j))‖ := by
      rw [← inverse_fourier hζ]
    _ ≤ (n : ℝ)⁻¹ * ∑ i : ZMod n, R := by
      rw [norm_mul,norm_inv,Complex.norm_natCast]
      gcongr
      exact (norm_sum_le _ _).trans (sum_le_sum (fun i _ ↦ by
        simpa only [norm_mul,rootChar_norm,mul_one] using hR i))
    _ = R := by simp [ZMod.card]; field_simp

/-- Actual coefficient bound for a family satisfying the conjugate power equation. -/
theorem power_coefficient_bound (hζ : IsPrimitiveRoot ζ n) (m : ℕ) (hm : m≠0)
    (ρ A R s : ℝ) (hρ : 0<ρ) (hA : 0≤A) (hR : 0≤R) (hRm : R^m=A+ρ)
    (hs : |s|=1) (c : ZMod n → ℤ)
    (heq : ∀ i : ZMod n, gammaPower ρ c ζ i ^ m =
      (A : ℂ)-(s : ℂ)*(ρ : ℂ)*rootChar hζ.pow_eq_one i) (j : ZMod n) :
    |(c j : ℝ)| ≤ R / ρ^j.val := by
  apply (le_div_iff₀ (pow_pos hρ _)).mpr
  have h := coefficient_bound hζ (weightedCoefficients ρ c) R (fun i ↦ by
    rw [gamma_eq_gammaPower]
    exact norm_of_power_le m hm A ρ R s hA hρ.le hR hRm _ _ (rootChar_norm _ _) hs (heq i)) j
  simpa only [weightedCoefficients,abs_mul,abs_of_pos (pow_pos hρ _)] using h

/-- In the small-height strip every nonconstant integer coefficient has absolute value < m. -/
theorem strip_coefficient_lt (hζ : IsPrimitiveRoot ζ n) (m : ℕ) (hm : 0<m)
    (ρ A R s : ℝ) (hρ : 1<ρ) (hA : 0≤A) (hR : 0≤R) (hRm : R^m=A+ρ)
    (hstrip : A+ρ<((m : ℝ)*ρ)^m) (hs : |s|=1) (c : ZMod n → ℤ)
    (heq : ∀ i : ZMod n, gammaPower ρ c ζ i ^ m =
      (A : ℂ)-(s : ℂ)*(ρ : ℂ)*rootChar hζ.pow_eq_one i)
    (j : ZMod n) (hj : j≠0) : |(c j : ℝ)| < m := by
  have hρ₀ : 0<ρ := lt_trans zero_lt_one hρ
  have hRlt : R < (m : ℝ)*ρ := by
    apply (pow_lt_pow_iff_left₀ hR (by positivity) hm.ne').mp
    simpa only [hRm] using hstrip
  have hjval : 1≤j.val := by
    have := mt (ZMod.val_eq_zero j).mp hj
    omega
  have hpow : ρ≤ρ^j.val := by
    simpa using pow_le_pow_right₀ hρ.le hjval
  have hc := power_coefficient_bound hζ m hm.ne' ρ A R s hρ₀ hA hR hRm hs c heq j
  have hmul := (le_div_iff₀ (pow_pos hρ₀ _)).mp hc
  have hcompare : |(c j : ℝ)| * ρ ≤ |(c j : ℝ)| * ρ^j.val :=
    mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
  exact (mul_lt_mul_iff_left₀ hρ₀).mp (lt_of_le_of_lt hcompare (lt_of_le_of_lt hmul hRlt))
end PillaiCoefficients
