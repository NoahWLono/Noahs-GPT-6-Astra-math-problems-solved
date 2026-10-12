import FiniteFourier

/-!
A precise bridge from finite cyclic autocorrelation to the integer power-basis
expressions used in the scoped Pillai paper. These results do not require the
large-height assumptions, nor a prime n: every nonzero n works.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Complex

namespace PillaiFourier

variable {n : ℕ} [NeZero n] {ζ : ℂ}

/-- Power-basis coefficients evaluated at a real radius. -/
noncomputable def weightedCoefficients (ρ : ℝ) (c : ZMod n → ℤ) (j : ZMod n) : ℝ :=
  (c j : ℝ) * ρ ^ j.val

/-- The explicit n conjugate-like evaluations; i and j range over 0,...,n−1. -/
noncomputable def gammaPower (ρ : ℝ) (c : ZMod n → ℤ) (ζ : ℂ) (i : ZMod n) : ℂ :=
  ∑ j : ZMod n, (c j : ℂ) * (ρ : ℂ) ^ j.val * ζ ^ (i.val * j.val)

/-- The explicit filtered power-basis polynomial, evaluated at ρ ζ^h. -/
noncomputable def betaPower (ρ : ℝ) (c : ZMod n → ℤ) (ζ : ℂ)
    (r h : ZMod n) : ℂ :=
  ∑ j : ZMod n, ∑ t : ZMod n with j - t = r,
    (c j : ℂ) * (c t : ℂ) * ((ρ : ℂ) * ζ ^ h.val) ^ (j.val + t.val)

lemma rootChar_mul_val (hζ : ζ ^ n = 1) (i j : ZMod n) :
    rootChar hζ (i * j) = ζ ^ (i.val * j.val) := by
  have heq : ((i.val * j.val : ℕ) : ZMod n) = i * j := by simp
  rw [← heq, rootChar_natCast]

lemma rootChar_twist_val (hζ : ζ ^ n = 1) (h j t : ZMod n) :
    rootChar hζ (h * (j + t)) = (ζ ^ h.val) ^ (j.val + t.val) := by
  have heq : ((h.val * (j.val + t.val) : ℕ) : ZMod n) = h * (j + t) := by simp
  rw [← heq, rootChar_natCast, pow_mul]

/-- The gamma definition is exactly the explicit positive-phase polynomial evaluation. -/
theorem gamma_eq_gammaPower (hζ : ζ ^ n = 1) (ρ : ℝ) (c : ZMod n → ℤ)
    (i : ZMod n) :
    gamma hζ (weightedCoefficients ρ c) i = gammaPower ρ c ζ i := by
  simp only [gamma, gammaPower, weightedCoefficients, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_intCast, rootChar_mul_val]

/-- The cyclic single-sum expression equals the original filtered double sum. -/
theorem betaPower_eq_twisted (hζ : ζ ^ n = 1) (ρ : ℝ) (c : ZMod n → ℤ)
    (r h : ZMod n) :
    betaPower ρ c ζ r h = twistedAutocorrelation hζ (weightedCoefficients ρ c) r h := by
  classical
  have hfilter (j t : ZMod n) : j - t = r ↔ t = j - r := by
    constructor <;> intro h <;> linear_combination -h
  simp only [betaPower, hfilter, sum_filter, sum_ite_eq', mem_univ, if_true,
    twistedAutocorrelation, weightedCoefficients, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_intCast, rootChar_twist_val]
  apply sum_congr rfl
  intro j _
  rw [mul_pow, pow_add (ρ : ℂ)]
  ring

/-- Coefficient energy is the sum c_j²ρ^(2j) from the paper. -/
theorem weighted_energy (ρ : ℝ) (c : ZMod n → ℤ) :
    ∑ j : ZMod n, weightedCoefficients ρ c j ^ 2 =
      ∑ j : ZMod n, (c j : ℝ) ^ 2 * ρ ^ (2 * j.val) := by
  apply sum_congr rfl
  intro j _
  simp only [weightedCoefficients, mul_pow, ← pow_mul, Nat.mul_comm]

/-- The real embedding is the normalized Fourier coefficient at r. -/
theorem betaPower_zero_fourier (hζ : IsPrimitiveRoot ζ n) (ρ : ℝ)
    (c : ZMod n → ℤ) (r : ZMod n) :
    betaPower ρ c ζ r 0 =
      (n : ℂ)⁻¹ * ∑ i : ZMod n, (‖gammaPower ρ c ζ i‖ ^ 2 : ℂ) *
        rootChar hζ.pow_eq_one (-(i * r)) := by
  rw [betaPower_eq_twisted hζ.pow_eq_one]
  simp only [twistedAutocorrelation, zero_mul, AddChar.map_zero_eq_one, mul_one]
  rw [autocorrelation_fourier hζ]
  simp_rw [gamma_eq_gammaPower]

/-- Bound for every conjugate, with the exact coefficient energy on the right. -/
theorem betaPower_bound (hζ : ζ ^ n = 1) (ρ : ℝ) (c : ZMod n → ℤ)
    (r h : ZMod n) :
    ‖betaPower ρ c ζ r h‖ ≤ ∑ j : ZMod n, (c j : ℝ) ^ 2 * ρ ^ (2 * j.val) := by
  rw [betaPower_eq_twisted hζ, ← weighted_energy]
  exact twistedAutocorrelation_bound hζ _ r h

/-- Parseval in the paper's integer power-basis coordinates. -/
theorem powerBasis_parseval (hζ : IsPrimitiveRoot ζ n) (ρ : ℝ) (c : ZMod n → ℤ) :
    (∑ j : ZMod n, (c j : ℝ) ^ 2 * ρ ^ (2 * j.val)) =
      (n : ℝ)⁻¹ * ∑ i : ZMod n, ‖gammaPower ρ c ζ i‖ ^ 2 := by
  rw [← weighted_energy, parseval hζ]
  simp_rw [gamma_eq_gammaPower]

lemma rootChar_intCast (hζ : ζ ^ n = 1) (j : ℤ) :
    rootChar hζ (j : ZMod n) = ζ ^ j := by
  have hone : rootChar hζ (1 : ZMod n) = ζ := by
    simpa using rootChar_natCast hζ 1
  calc
    rootChar hζ (j : ZMod n) = rootChar hζ (j • (1 : ZMod n)) := by
      rw [zsmul_eq_mul, mul_one]
    _ = (rootChar hζ (1 : ZMod n)) ^ j := AddChar.map_zsmul_eq_zpow _ _ _
    _ = ζ ^ j := by rw [hone]

lemma rootChar_negative_second (hζ : ζ ^ n = 1) (i : ZMod n) :
    rootChar hζ (-(i * 2)) = ζ ^ (-(2 * (i.val : ℤ))) := by
  have heq : ((-(2 * (i.val : ℤ)) : ℤ) : ZMod n) = -(i * 2) := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
    ring
  rw [← heq, rootChar_intCast]

/-- Exactly the paper's second-mode identity, including its negative sign and 1/n. -/
theorem second_mode_identity (hζ : IsPrimitiveRoot ζ n) (ρ : ℝ) (c : ZMod n → ℤ) :
    betaPower ρ c ζ 2 0 =
      (n : ℂ)⁻¹ * ∑ i : ZMod n, (‖gammaPower ρ c ζ i‖ ^ 2 : ℂ) *
        ζ ^ (-(2 * (i.val : ℤ))) := by
  rw [betaPower_zero_fourier hζ]
  simp_rw [rootChar_negative_second]

/-- The complete finite Fourier/energy interface requested for second mode.
This is stronger than the n≥5, ρ>0 specialization: those hypotheses are unused.
It asserts no nonvanishing and no irreducibility claim. -/
theorem second_mode_interface (hζ : IsPrimitiveRoot ζ n) (ρ : ℝ) (c : ZMod n → ℤ) :
    (betaPower ρ c ζ 2 0 =
      (n : ℂ)⁻¹ * ∑ i : ZMod n, (‖gammaPower ρ c ζ i‖ ^ 2 : ℂ) *
        ζ ^ (-(2 * (i.val : ℤ)))) ∧
    (∀ h : ZMod n, ‖betaPower ρ c ζ 2 h‖ ≤
      ∑ j : ZMod n, (c j : ℝ) ^ 2 * ρ ^ (2 * j.val)) ∧
    ((∑ j : ZMod n, (c j : ℝ) ^ 2 * ρ ^ (2 * j.val)) =
      (n : ℝ)⁻¹ * ∑ i : ZMod n, ‖gammaPower ρ c ζ i‖ ^ 2) := by
  exact ⟨second_mode_identity hζ ρ c,
    fun h ↦ betaPower_bound hζ.pow_eq_one ρ c 2 h, powerBasis_parseval hζ ρ c⟩

end PillaiFourier
