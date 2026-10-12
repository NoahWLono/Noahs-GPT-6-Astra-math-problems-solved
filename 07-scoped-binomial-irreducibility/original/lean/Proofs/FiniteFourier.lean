import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
Finite autocorrelation identities for an arbitrary primitive complex root of unity.
The Fourier transform has positive phase and is not normalized.
No arithmetic irreducibility theorem is asserted in this module.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Complex

namespace PillaiFourier

variable {n : ℕ} [NeZero n] {ζ : ℂ}

/-- The additive character defined by an explicitly supplied root of unity. -/
def rootChar (hζ : ζ ^ n = 1) : AddChar (ZMod n) ℂ where
  toFun a := ζ ^ a.val
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [ZMod.val_add, ← pow_eq_pow_mod _ hζ, ← pow_add]

lemma rootChar_natCast (hζ : ζ ^ n = 1) (j : ℕ) :
    rootChar hζ (j : ZMod n) = ζ ^ j := by
  change ζ ^ (j : ZMod n).val = ζ ^ j
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]

lemma rootChar_norm (hζ : ζ ^ n = 1) (x : ZMod n) :
    ‖rootChar hζ x‖ = 1 := by
  change ‖ζ ^ x.val‖ = 1
  rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one hζ (NeZero.ne n), one_pow]

lemma rootChar_conj (hζ : ζ ^ n = 1) (x : ZMod n) :
    (starRingEnd ℂ) (rootChar hζ x) = rootChar hζ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (rootChar_norm hζ x)]

lemma rootChar_eq_one_iff (hζ : IsPrimitiveRoot ζ n) (x : ZMod n) :
    rootChar hζ.pow_eq_one x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    have hval : x.val = 0 := hζ.pow_inj (ZMod.val_lt x) (NeZero.pos n)
      (by simpa [rootChar] using hx)
    exact (ZMod.val_eq_zero x).mp hval
  · rintro rfl
    exact AddChar.map_zero_eq_one _

/-- Exact character orthogonality, with no Fourier identity assumed. -/
theorem rootChar_orthogonality (hζ : IsPrimitiveRoot ζ n) (k : ZMod n) :
    ∑ i : ZMod n, rootChar hζ.pow_eq_one (i * k) =
      if k = 0 then (n : ℂ) else 0 := by
  classical
  by_cases hk : k = 0
  · simp [hk, ZMod.card]
  · simp only [hk, if_false]
    let S : ℂ := ∑ i : ZMod n, rootChar hζ.pow_eq_one (i * k)
    have hs : S * rootChar hζ.pow_eq_one k = S := by
      dsimp [S]
      rw [sum_mul]
      simp_rw [← AddChar.map_add_eq_mul]
      calc
        ∑ i : ZMod n, rootChar hζ.pow_eq_one (i * k + k) =
            ∑ i : ZMod n, rootChar hζ.pow_eq_one ((i + 1) * k) := by
          congr 1 with i
          rw [add_mul, one_mul]
        _ = ∑ i : ZMod n, rootChar hζ.pow_eq_one (i * k) :=
          Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ ↦ rfl)
    have hc : rootChar hζ.pow_eq_one k ≠ 1 :=
      mt (rootChar_eq_one_iff hζ k).mp hk
    change S = 0
    have hz : S * (rootChar hζ.pow_eq_one k - 1) = 0 := by
      calc
        _ = S * rootChar hζ.pow_eq_one k - S := by ring
        _ = 0 := by rw [hs, sub_self]
    exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hc)

/-- Positive-phase unnormalized finite Fourier transform of real coefficients. -/
noncomputable def gamma (hζ : ζ ^ n = 1) (a : ZMod n → ℝ) (i : ZMod n) : ℂ :=
  ∑ j : ZMod n, (a j : ℂ) * rootChar hζ (i * j)

lemma gamma_norm_sq (hζ : ζ ^ n = 1) (a : ZMod n → ℝ) (i : ZMod n) :
    (‖gamma hζ a i‖ ^ 2 : ℂ) =
      ∑ j : ZMod n, ∑ t : ZMod n,
        (a j : ℂ) * (a t : ℂ) * rootChar hζ (i * (j - t)) := by
  rw [← Complex.mul_conj']
  simp only [gamma, map_sum, map_mul, Complex.conj_ofReal, rootChar_conj]
  rw [sum_mul]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro t _
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
  congr 2
  ring

lemma rootChar_phase (hζ : ζ ^ n = 1) (i j t r : ZMod n) :
    rootChar hζ (i * (j - t)) * rootChar hζ (-(i * r)) =
      rootChar hζ (i * (j - t - r)) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The unnormalized power-spectrum coefficient is n times autocorrelation. -/
theorem spectrum_sum (hζ : IsPrimitiveRoot ζ n) (a : ZMod n → ℝ) (r : ZMod n) :
    ∑ i : ZMod n, (‖gamma hζ.pow_eq_one a i‖ ^ 2 : ℂ) *
      rootChar hζ.pow_eq_one (-(i * r)) =
        (n : ℂ) * ∑ j : ZMod n, (a j : ℂ) * (a (j - r) : ℂ) := by
  classical
  simp_rw [gamma_norm_sq, sum_mul, mul_assoc, rootChar_phase]
  rw [sum_comm]
  calc
    ∑ j : ZMod n, ∑ i : ZMod n, ∑ t : ZMod n,
        (a j : ℂ) * ((a t : ℂ) * rootChar hζ.pow_eq_one (i * (j - t - r))) =
      ∑ j : ZMod n, ∑ t : ZMod n, (a j : ℂ) * (a t : ℂ) *
        (∑ i : ZMod n, rootChar hζ.pow_eq_one (i * (j - t - r))) := by
      apply sum_congr rfl
      intro j _
      rw [sum_comm]
      apply sum_congr rfl
      intro t _
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ = (n : ℂ) * ∑ j : ZMod n, (a j : ℂ) * (a (j - r) : ℂ) := by
      simp_rw [rootChar_orthogonality hζ]
      have heq (j t : ZMod n) : j - t - r = 0 ↔ t = j - r := by
        constructor <;> intro h <;> linear_combination -h
      simp_rw [heq, mul_ite, mul_zero]
      simp only [sum_ite_eq', mem_univ, if_true]
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring

/-- Normalized power-spectrum/autocorrelation identity at every cyclic frequency. -/
theorem autocorrelation_fourier (hζ : IsPrimitiveRoot ζ n) (a : ZMod n → ℝ)
    (r : ZMod n) :
    (∑ j : ZMod n, (a j : ℂ) * (a (j - r) : ℂ)) =
      (n : ℂ)⁻¹ * ∑ i : ZMod n, (‖gamma hζ.pow_eq_one a i‖ ^ 2 : ℂ) *
        rootChar hζ.pow_eq_one (-(i * r)) := by
  rw [spectrum_sum hζ, ← mul_assoc, inv_mul_cancel₀ (NeZero.ne (n : ℂ)), one_mul]

/-- Parseval with the precise normalization for the unnormalized transform. -/
theorem parseval (hζ : IsPrimitiveRoot ζ n) (a : ZMod n → ℝ) :
    (∑ j : ZMod n, a j ^ 2) =
      (n : ℝ)⁻¹ * ∑ i : ZMod n, ‖gamma hζ.pow_eq_one a i‖ ^ 2 := by
  have hc := autocorrelation_fourier hζ a 0
  apply Complex.ofReal_injective
  simpa [pow_two] using hc

lemma sum_sub_right (f : ZMod n → ℝ) (r : ZMod n) :
    ∑ j : ZMod n, f (j - r) = ∑ j : ZMod n, f j := by
  simpa only [sub_eq_add_neg] using
    Fintype.sum_equiv (Equiv.addRight (-r)) (fun j ↦ f (j + -r)) f (fun _ ↦ rfl)

/-- The same autocorrelation polynomial evaluated at the h-th root-of-unity twist. -/
noncomputable def twistedAutocorrelation (hζ : ζ ^ n = 1) (a : ZMod n → ℝ)
    (r h : ZMod n) : ℂ :=
  ∑ j : ZMod n, (a j : ℂ) * (a (j - r) : ℂ) * rootChar hζ (h * (j + (j - r)))

/-- Every root-of-unity twist is bounded by the same coefficient energy. -/
theorem twistedAutocorrelation_bound (hζ : ζ ^ n = 1) (a : ZMod n → ℝ)
    (r h : ZMod n) :
    ‖twistedAutocorrelation hζ a r h‖ ≤ ∑ j : ZMod n, a j ^ 2 := by
  classical
  calc
    ‖twistedAutocorrelation hζ a r h‖ ≤
        ∑ j : ZMod n, ‖(a j : ℂ) * (a (j - r) : ℂ) *
          rootChar hζ (h * (j + (j - r)))‖ := norm_sum_le _ _
    _ = ∑ j : ZMod n, |a j| * |a (j - r)| := by
      simp only [norm_mul, rootChar_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ j : ZMod n, (a j ^ 2 + a (j - r) ^ 2) / 2 := by
      apply sum_le_sum
      intro j _
      nlinarith [sq_nonneg (|a j| - |a (j - r)|), sq_abs (a j), sq_abs (a (j - r))]
    _ = ∑ j : ZMod n, a j ^ 2 := by
      simp_rw [div_eq_mul_inv]
      rw [← sum_mul, sum_add_distrib, sum_sub_right (fun j ↦ a j ^ 2)]
      ring

end PillaiFourier
