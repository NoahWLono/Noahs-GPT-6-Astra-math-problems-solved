import HeightBounds
import ConjugateEquation

/-! Exact complex-norm normalization and scaling of the proved Taylor/Fourier estimate. -/

set_option autoImplicit false
open scoped BigOperators
open Finset Complex
open PillaiFourier PillaiTaylor PillaiTaylorFourier

namespace PillaiSamples

lemma norm_shift_square (A ρ s : ℝ) (w : ℂ) (hw : ‖w‖ = 1) (hs : s=1 ∨ s= -1) :
    ‖(A : ℂ) - (s : ℂ)*(ρ : ℂ)*w‖^2 = A^2 - 2*s*A*ρ*w.re + ρ^2 := by
  have hw' : w.re^2+w.im^2=1 := by
    have h := congrArg (fun x : ℝ ↦ x^2) hw
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply] at h
    simpa [pow_two] using h
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
  rcases hs with rfl | rfl <;> linear_combination (ρ^2)*hw'

lemma norm_of_power_le (m : ℕ) (hm : m ≠ 0) (A ρ R s : ℝ)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (hRm : R^m=A+ρ)
    (z w : ℂ) (hw : ‖w‖=1) (hs : |s|=1)
    (hz : z^m=(A : ℂ)-(s : ℂ)*(ρ : ℂ)*w) : ‖z‖ ≤ R := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg z) hR hm).mp
  calc
    ‖z‖^m = ‖z^m‖ := (norm_pow _ _).symm
    _ = ‖(A : ℂ)-(s : ℂ)*(ρ : ℂ)*w‖ := by rw [hz]
    _ ≤ ‖(A : ℂ)‖+‖(s : ℂ)*(ρ : ℂ)*w‖ := norm_sub_le _ _
    _ = A+ρ := by simp [Complex.norm_real,Real.norm_eq_abs,hs,hw,abs_of_nonneg hA,abs_of_nonneg hρ]
    _ = R^m := hRm.symm

/-- Taking real nonnegative m-th roots gives the exact normalized squared norm. -/
theorem norm_sq_power_sample (m : ℕ) (hm : m ≠ 0) (A ρ S s : ℝ)
    (hA : 0 < A) (hS : S^m=A) (hs : s=1 ∨ s= -1)
    (hu : 0 ≤ ρ/A) (hu₁ : ρ/A ≤ 1/4) (z w : ℂ) (hw : ‖w‖=1)
    (hz : z^m=(A : ℂ)-(s : ℂ)*(ρ : ℂ)*w) :
    ‖z‖^2 = S^2 * (1-2*s*w.re*(ρ/A)+(ρ/A)^2)^((m : ℝ)⁻¹) := by
  let H := 1-2*s*w.re*(ρ/A)+(ρ/A)^2
  have hsabs : |s|=1 := by rcases hs with rfl | rfl <;> norm_num
  have hb : |s*w.re| ≤ 1 := by
    rw [abs_mul,hsabs,one_mul]
    simpa [hw] using Complex.abs_re_le_norm w
  have hH : 0 ≤ H := by
    have h := (quad_bounds (s*w.re) (ρ/A) hb ⟨hu,hu₁⟩).1
    dsimp [quad] at h
    dsimp [H]
    nlinarith
  have hnorm : ‖(A : ℂ)-(s : ℂ)*(ρ : ℂ)*w‖^2 = A^2*H := by
    rw [norm_shift_square A ρ s w hw hs]
    dsimp [H]
    field_simp
  apply (pow_left_inj₀ (sq_nonneg ‖z‖)
    (mul_nonneg (sq_nonneg S) (Real.rpow_nonneg hH _)) hm).mp
  have hleft : (‖z‖^2)^m = A^2*H := by
    rw [← pow_mul,Nat.mul_comm 2 m,pow_mul,← norm_pow,hz,hnorm]
  have hright : (S^2)^m = A^2 := by
    rw [← pow_mul,Nat.mul_comm 2 m,pow_mul,hS]
  rw [hleft,mul_pow,hright,Real.rpow_inv_natCast_pow hH hm]

variable {n : ℕ} [NeZero n] {ζ : ℂ}

/-- Exact scaling back from the normalized analytic mode to the power-basis beta. -/
theorem beta_scaled_mode (hζ : IsPrimitiveRoot ζ n) (m : ℕ) (hm : m ≠ 0)
    (ρ A S s : ℝ) (hA : 0 < A) (hS : S^m=A) (hs : s=1 ∨ s= -1)
    (hu : 0 ≤ ρ/A) (hu₁ : ρ/A ≤ 1/4) (c : ZMod n → ℤ)
    (heq : ∀ i : ZMod n, gammaPower ρ c ζ i ^ m =
      (A : ℂ)-(s : ℂ)*(ρ : ℂ)*rootChar hζ.pow_eq_one i) :
    betaPower ρ c ζ 2 0 = (S^2 : ℝ) * powerMode₂ hζ.pow_eq_one ((m : ℝ)⁻¹) s (ρ/A) := by
  have hnorm (i : ZMod n) : ‖gammaPower ρ c ζ i‖^2 =
      S^2*powerSample hζ.pow_eq_one ((m : ℝ)⁻¹) s (ρ/A) i := by
    exact norm_sq_power_sample m hm A ρ S s hA hS hs hu hu₁ _ _ (rootChar_norm _ _) (heq i)
  rw [betaPower_zero_fourier hζ]
  simp only [powerMode₂,mode₂_apply]
  simp_rw [← Complex.ofReal_pow,hnorm,Complex.ofReal_mul,mul_assoc]
  rw [← mul_sum]
  ring

/-- The coefficient energy and every beta twist are bounded by the common root radius. -/
theorem beta_all_bound (hζ : IsPrimitiveRoot ζ n) (m : ℕ) (hm : m ≠ 0)
    (ρ A R s : ℝ) (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (hRm : R^m=A+ρ)
    (hs : |s|=1) (c : ZMod n → ℤ)
    (heq : ∀ i : ZMod n, gammaPower ρ c ζ i ^ m =
      (A : ℂ)-(s : ℂ)*(ρ : ℂ)*rootChar hζ.pow_eq_one i) :
    ∀ h : ZMod n, ‖betaPower ρ c ζ 2 h‖ ≤ R^2 := by
  intro h
  apply (betaPower_bound hζ.pow_eq_one ρ c 2 h).trans
  rw [powerBasis_parseval hζ]
  calc
    (n : ℝ)⁻¹ * ∑ i : ZMod n, ‖gammaPower ρ c ζ i‖^2 ≤
        (n : ℝ)⁻¹ * ∑ _i : ZMod n, R^2 := by
      gcongr with i
      exact norm_of_power_le m hm A ρ R s hA hρ hR hRm _ _ (rootChar_norm _ _) hs (heq i)
    _ = R^2 := by simp [ZMod.card,nsmul_eq_mul,← mul_assoc]

/-- The actual beta at the real root is nonzero and has the small bound needed for the product. -/
theorem beta_zero_small (hζ : IsPrimitiveRoot ζ n) (hn : 5 ≤ n) (m : ℕ) (hm : n<m)
    (ρ A R S s : ℝ) (hA : 0 < A) (_hR : 0 ≤ R) (hSpos : 0 < S)
    (hS : S^m=A) (hSR : S ≤ R) (hs : s=1 ∨ s= -1)
    (hu : 0 < ρ/A) (hu₁ : ρ/A < 1/1000) (c : ZMod n → ℤ)
    (heq : ∀ i : ZMod n, gammaPower ρ c ζ i ^ m =
      (A : ℂ)-(s : ℂ)*(ρ : ℂ)*rootChar hζ.pow_eq_one i) :
    0 < ‖betaPower ρ c ζ 2 0‖ ∧ ‖betaPower ρ c ζ 2 0‖ < ρ^2*R^2/((m : ℝ)*A^2) := by
  have hm₀ : m ≠ 0 := by omega
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hscaled := beta_scaled_mode hζ m hm₀ ρ A S s hA hS hs hu.le (by linarith) c heq
  have hmode := (reciprocal_second_mode hζ hn m hm s (ρ/A) hs hu hu₁).2
  have hnorm : ‖betaPower ρ c ζ 2 0‖ = S^2*‖powerMode₂ hζ.pow_eq_one ((m : ℝ)⁻¹) s (ρ/A)‖ := by
    rw [hscaled,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg S)]
  rw [hnorm]
  refine ⟨mul_pos (sq_pos_of_pos hSpos) hmode.1,?_⟩
  calc
    S^2*‖powerMode₂ hζ.pow_eq_one ((m : ℝ)⁻¹) s (ρ/A)‖ <
        S^2*((m : ℝ)⁻¹*(ρ/A)^2) := mul_lt_mul_of_pos_left hmode.2 (sq_pos_of_pos hSpos)
    _ ≤ R^2*((m : ℝ)⁻¹*(ρ/A)^2) := by gcongr
    _ = ρ^2*R^2/((m : ℝ)*A^2) := by field_simp

end PillaiSamples
