import FiniteTaylor
import PillaiPowerBasis

/-! Quantitative second Fourier mode of the concrete real-power samples. -/

set_option autoImplicit false
open scoped BigOperators
open Finset Complex
open PillaiFourier PillaiTaylor

namespace PillaiTaylorFourier

variable {n : ℕ} [NeZero n] {ζ : ℂ}

/-- The normalized second Fourier coefficient as a complex-linear functional. -/
noncomputable def mode₂ (hζ : ζ ^ n = 1) : (ZMod n → ℂ) →ₗ[ℂ] ℂ where
  toFun f := (n : ℂ)⁻¹ * ∑ i : ZMod n, f i * rootChar hζ (-(i*2))
  map_add' f g := by
    simp only [Pi.add_apply, add_mul, sum_add_distrib, mul_add]
  map_smul' z f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← mul_sum]
    ring

lemma mode₂_apply (hζ : ζ ^ n = 1) (f : ZMod n → ℂ) :
    mode₂ hζ f = (n : ℂ)⁻¹ * ∑ i : ZMod n, f i * rootChar hζ (-(i*2)) := rfl

lemma mode₂_character (hζ : IsPrimitiveRoot ζ n) (k : ZMod n) :
    mode₂ hζ.pow_eq_one (fun i ↦ rootChar hζ.pow_eq_one (i*k)) =
      if k = 2 then 1 else 0 := by
  classical
  rw [mode₂_apply]
  have hp (i : ZMod n) : rootChar hζ.pow_eq_one (i*k) * rootChar hζ.pow_eq_one (-(i*2)) =
      rootChar hζ.pow_eq_one (i*(k-2)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hp]
  rw [rootChar_orthogonality hζ]
  by_cases hk : k = 2 <;> simp [hk, sub_eq_zero]

omit [NeZero n] in
lemma small_natCast_ne_zero (hn : 5 ≤ n) (k : ℕ) (hk : 0 < k) (hk₁ : k ≤ 4) :
    (k : ZMod n) ≠ 0 := by
  intro he
  have he' := congrArg ZMod.val he
  have hkn : k < n := by omega
  rw [ZMod.val_natCast_of_lt hkn,ZMod.val_zero] at he'
  omega

omit [NeZero n] in
lemma frequencies_distinct (hn : 5 ≤ n) :
    (0 : ZMod n) ≠ 2 ∧ (1 : ZMod n) ≠ 2 ∧ (-1 : ZMod n) ≠ 2 ∧ (-2 : ZMod n) ≠ 2 := by
  have h₁ := small_natCast_ne_zero hn 1 (by omega) (by omega)
  have h₂ := small_natCast_ne_zero hn 2 (by omega) (by omega)
  have h₃ := small_natCast_ne_zero hn 3 (by omega) (by omega)
  have h₄ := small_natCast_ne_zero hn 4 (by omega) (by omega)
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at h₁ h₂ h₃ h₄
  refine ⟨Ne.symm h₂,?_,?_,?_⟩
  · intro he; apply h₁; linear_combination -he
  · intro he; apply h₃; linear_combination -he
  · intro he; apply h₄; linear_combination -he

/-- The real coordinate of the i-th root of unity. -/
noncomputable def circleX (hζ : ζ ^ n = 1) (i : ZMod n) : ℝ := (rootChar hζ i).re

lemma circleX_bound (hζ : ζ ^ n = 1) (i : ZMod n) : |circleX hζ i| ≤ 1 := by
  simpa only [circleX, rootChar_norm] using Complex.abs_re_le_norm (rootChar hζ i)

lemma circleX_expansion (hζ : ζ ^ n = 1) (i : ZMod n) :
    (circleX hζ i : ℂ) = (rootChar hζ i + rootChar hζ (-i)) / 2 := by
  rw [circleX,Complex.re_eq_add_conj,rootChar_conj]

lemma circleX_sq_expansion (hζ : ζ ^ n = 1) (i : ZMod n) :
    ((circleX hζ i : ℂ)^2) =
      (rootChar hζ (i*2) + 2*rootChar hζ (i*0) + rootChar hζ (i*(-2))) / 4 := by
  rw [circleX_expansion]
  have h₁ : rootChar hζ i * rootChar hζ i = rootChar hζ (i*2) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have h₂ : rootChar hζ (-i) * rootChar hζ (-i) = rootChar hζ (i*(-2)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have h₀ : rootChar hζ i * rootChar hζ (-i) = rootChar hζ (i*0) := by
    rw [← AddChar.map_add_eq_mul]
    simp
  calc
    _ = (rootChar hζ i * rootChar hζ i + 2*(rootChar hζ i * rootChar hζ (-i)) +
      rootChar hζ (-i)*rootChar hζ (-i))/4 := by ring
    _ = _ := by rw [h₁,h₀,h₂]

lemma mode₂_const_one (hζ : IsPrimitiveRoot ζ n) (hn : 5 ≤ n) :
    mode₂ hζ.pow_eq_one (fun _ ↦ 1) = 0 := by
  have hf := mode₂_character hζ 0
  simpa [(frequencies_distinct hn).1] using hf

lemma mode₂_circleX (hζ : IsPrimitiveRoot ζ n) (hn : 5 ≤ n) :
    mode₂ hζ.pow_eq_one (fun i ↦ (circleX hζ.pow_eq_one i : ℂ)) = 0 := by
  have he : (fun i ↦ (circleX hζ.pow_eq_one i : ℂ)) =
      (1/2 : ℂ) • ((fun i ↦ rootChar hζ.pow_eq_one (i*1)) +
        (fun i ↦ rootChar hζ.pow_eq_one (i*(-1)))) := by
    funext i
    rw [circleX_expansion]
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul,mul_one,mul_neg_one]
    ring
  rw [he,map_smul,map_add,mode₂_character hζ,mode₂_character hζ]
  simp [(frequencies_distinct hn).2.1,(frequencies_distinct hn).2.2.1]

lemma mode₂_circleX_sq (hζ : IsPrimitiveRoot ζ n) (hn : 5 ≤ n) :
    mode₂ hζ.pow_eq_one (fun i ↦ (circleX hζ.pow_eq_one i : ℂ)^2) = 1/4 := by
  have he : (fun i ↦ (circleX hζ.pow_eq_one i : ℂ)^2) =
      (1/4 : ℂ) • ((fun i ↦ rootChar hζ.pow_eq_one (i*2)) +
        (2 : ℂ) • (fun i ↦ rootChar hζ.pow_eq_one (i*0)) +
        (fun i ↦ rootChar hζ.pow_eq_one (i*(-2)))) := by
    funext i
    rw [circleX_sq_expansion]
    simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  rw [he,map_smul,map_add,map_add,map_smul]
  simp only [mode₂_character hζ,ite_true]
  simp [(frequencies_distinct hn).1,(frequencies_distinct hn).2.2.2]

/-- The normalized Fourier coefficient has operator norm at most one for the sup norm. -/
lemma mode₂_bound (hζ : ζ ^ n = 1) (f : ZMod n → ℂ) (C : ℝ)
    (hf : ∀ i, ‖f i‖ ≤ C) : ‖mode₂ hζ f‖ ≤ C := by
  rw [mode₂_apply,norm_mul,norm_inv,norm_natCast]
  calc
    (n : ℝ)⁻¹ * ‖∑ i : ZMod n, f i * rootChar hζ (-(i*2))‖ ≤
        (n : ℝ)⁻¹ * ∑ i : ZMod n, ‖f i * rootChar hζ (-(i*2))‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (n : ℝ)⁻¹ * ∑ i : ZMod n, ‖f i‖ := by simp only [norm_mul,rootChar_norm,mul_one]
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : ZMod n, C := by
      gcongr with i
      exact hf i
    _ = C := by simp [ZMod.card,nsmul_eq_mul,← mul_assoc]

noncomputable def quadraticApprox (a b u : ℝ) : ℝ :=
  1 - 2*a*b*u + (a + 2*a*(a-1)*b^2)*u^2

noncomputable def powerSample (hζ : ζ ^ n = 1) (a s u : ℝ) (i : ZMod n) : ℝ :=
  (1 - 2*s*circleX hζ i*u + u^2)^a

/-- The concrete second mode of the real-power samples. -/
noncomputable def powerMode₂ (hζ : ζ ^ n = 1) (a s u : ℝ) : ℂ :=
  mode₂ hζ (fun i ↦ (powerSample hζ a s u i : ℂ))

lemma mode₂_quadratic (hζ : IsPrimitiveRoot ζ n) (hn : 5 ≤ n)
    (a s u : ℝ) (hs : s = 1 ∨ s = -1) :
    mode₂ hζ.pow_eq_one (fun i ↦ (quadraticApprox a (s*circleX hζ.pow_eq_one i) u : ℂ)) =
      (a*(a-1)*u^2/2 : ℝ) := by
  have hs₂ : s^2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have he : (fun i ↦ (quadraticApprox a (s*circleX hζ.pow_eq_one i) u : ℂ)) =
      ((1+a*u^2 : ℝ) : ℂ) • (fun _ ↦ (1 : ℂ)) +
      ((-2*a*s*u : ℝ) : ℂ) • (fun i ↦ (circleX hζ.pow_eq_one i : ℂ)) +
      ((2*a*(a-1)*u^2 : ℝ) : ℂ) • (fun i ↦ (circleX hζ.pow_eq_one i : ℂ)^2) := by
    funext i
    simp only [quadraticApprox,mul_pow,hs₂,one_mul,Pi.add_apply,Pi.smul_apply,
      smul_eq_mul,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,
      Complex.ofReal_pow,Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_neg]
    ring
  rw [he,map_add,map_add,map_smul,map_smul,map_smul,mode₂_const_one hζ hn,
    mode₂_circleX hζ hn,mode₂_circleX_sq hζ hn]
  simp only [smul_eq_mul,mul_zero,add_zero,zero_add]
  push_cast
  ring

/-- The uniform Taylor estimate survives normalized second-mode averaging unchanged. -/
theorem powerMode₂_remainder (hζ : IsPrimitiveRoot ζ n) (hn : 5 ≤ n)
    (a s u : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1/6) (hs : s = 1 ∨ s = -1)
    (hu : 0 ≤ u) (hu₁ : u ≤ 1/4) :
    ‖powerMode₂ hζ.pow_eq_one a s u - (a*(a-1)*u^2/2 : ℝ)‖ ≤ 84*a*u^3 := by
  rw [powerMode₂,← mode₂_quadratic hζ hn a s u hs,← map_sub]
  apply mode₂_bound
  intro i
  simp only [Pi.sub_apply,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hb : |s*circleX hζ.pow_eq_one i| ≤ 1 := by
    rw [abs_mul,hsabs,one_mul]
    exact circleX_bound _ _
  simpa only [powerSample,quadraticApprox,mul_assoc] using
    quadratic_rpow_taylor a (s*circleX hζ.pow_eq_one i) u ha ha₁ hb hu hu₁

/-- An elementary norm estimate turning the exact error bound into nonvanishing. -/
lemma nonzero_of_remainder (a u : ℝ) (z : ℂ) (ha : 0 < a) (ha₁ : a ≤ 1/6)
    (hu : 0 < u) (hu₁ : u < 1/1000)
    (herr : ‖z - (a*(a-1)*u^2/2 : ℝ)‖ ≤ 84*a*u^3) :
    0 < ‖z‖ ∧ ‖z‖ < a*u^2 := by
  have hau : 0 < a*u^2 := by positivity
  have her : 84*a*u^3 < a*u^2/6 := by
    have hsmall : 84*u < 1/6 := by linarith
    have hh := mul_lt_mul_of_pos_left hsmall hau
    nlinarith
  have herr' := herr.trans_lt her
  have hL : ‖((a*(a-1)*u^2/2 : ℝ) : ℂ)‖ = a*(1-a)*u^2/2 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    have hh : a*(a-1)*u^2/2 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos ha.le (by linarith)) (sq_nonneg u)
    rw [abs_of_nonpos hh]
    ring
  have hLlo : a*u^2/3 ≤ ‖((a*(a-1)*u^2/2 : ℝ) : ℂ)‖ := by
    rw [hL]
    have hh := mul_nonneg (show (0 : ℝ) ≤ 1/3-a by linarith) hau.le
    nlinarith
  have hLhi : ‖((a*(a-1)*u^2/2 : ℝ) : ℂ)‖ ≤ a*u^2/2 := by
    rw [hL]
    nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg u)]
  have hlo := norm_sub_norm_le ((a*(a-1)*u^2/2 : ℝ) : ℂ) z
  rw [norm_sub_rev] at hlo
  have hhi := norm_sub_norm_le z ((a*(a-1)*u^2/2 : ℝ) : ℂ)
  constructor <;> linarith

/-- The concrete finite second Fourier coefficient is nonzero and has the required small norm. -/
theorem powerMode₂_nonzero (hζ : IsPrimitiveRoot ζ n) (hn : 5 ≤ n)
    (a s u : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1/6) (hs : s = 1 ∨ s = -1)
    (hu : 0 < u) (hu₁ : u < 1/1000) :
    0 < ‖powerMode₂ hζ.pow_eq_one a s u‖ ∧ ‖powerMode₂ hζ.pow_eq_one a s u‖ < a*u^2 := by
  exact nonzero_of_remainder a u _ ha ha₁ hu hu₁
    (powerMode₂_remainder hζ hn a s u ha ha₁ hs hu.le (by linarith))

/-- Explicit root-power expression, fixing the Fourier sign without referring to a character API. -/
theorem powerMode₂_explicit (hζ : ζ ^ n = 1) (a s u : ℝ) :
    powerMode₂ hζ a s u = (n : ℂ)⁻¹ * ∑ i : ZMod n,
      (((1 - 2*s*(ζ ^ i.val).re*u + u^2)^a : ℝ) : ℂ) * ζ ^ (-(2*(i.val : ℤ))) := by
  simp only [powerMode₂,mode₂_apply,powerSample,circleX,rootChar_negative_second]
  rfl

/-- Quantitative second-mode theorem for the paper's a=1/m parameters. -/
theorem reciprocal_second_mode (hζ : IsPrimitiveRoot ζ n) (hn : 5 ≤ n)
    (m : ℕ) (hm : n < m) (s u : ℝ) (hs : s = 1 ∨ s = -1)
    (hu : 0 < u) (hu₁ : u < 1/1000) :
    (‖powerMode₂ hζ.pow_eq_one ((m : ℝ)⁻¹) s u -
      (((m : ℝ)⁻¹*((m : ℝ)⁻¹-1)*u^2/2 : ℝ) : ℂ)‖ ≤ 84*((m : ℝ)⁻¹)*u^3) ∧
    (0 < ‖powerMode₂ hζ.pow_eq_one ((m : ℝ)⁻¹) s u‖) ∧
    (‖powerMode₂ hζ.pow_eq_one ((m : ℝ)⁻¹) s u‖ < ((m : ℝ)⁻¹)*u^2) := by
  have hm₆ : (6 : ℝ) ≤ m := by exact_mod_cast (show 6 ≤ m by omega)
  have hmpos : (0 : ℝ) < m := by linarith
  have ha : 0 < (m : ℝ)⁻¹ := inv_pos.mpr hmpos
  have ha₁ : (m : ℝ)⁻¹ ≤ 1/6 := by
    simpa only [one_div] using one_div_le_one_div_of_le (show (0 : ℝ) < 6 by norm_num) hm₆
  exact ⟨powerMode₂_remainder hζ hn _ s u ha ha₁ hs hu.le (by linarith),
    powerMode₂_nonzero hζ hn _ s u ha ha₁ hs hu hu₁⟩

end PillaiTaylorFourier
