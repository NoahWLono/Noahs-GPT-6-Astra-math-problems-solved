import IntegralPowerOrder
import AlgebraicPowerPropagation
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic

/-! Checked-stage helper for the scoped arithmetic composition assembly.
The final theorem must discharge every explicit helper premise. -/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace PillaiSignedRealExclusion

universe u

/-- For odd exponent, substitution X -> -X transfers irreducibility from
    X^n-k to X^n-(-k). The outer minus is a unit, not an extra assumption. -/
theorem irreducible_pure_binomial_neg
    (n : ℕ) (hn : Odd n) (k : ℤ)
    (hirr : Irreducible ((X : ℚ[X]) ^ n - C (k : ℚ))) :
    Irreducible ((X : ℚ[X]) ^ n - C ((-k : ℤ) : ℚ)) := by
  have hmap := (MulEquiv.irreducible_iff
    (Polynomial.algEquivAevalNegX (R := ℚ))).mpr hirr
  change Irreducible
    (aeval (-X : ℚ[X]) ((X : ℚ[X]) ^ n - C (k : ℚ))) at hmap
  have hsub : aeval (-X : ℚ[X]) ((X : ℚ[X]) ^ n - C (k : ℚ)) =
      (-1 : ℚ[X]) * ((X : ℚ[X]) ^ n - C ((-k : ℤ) : ℚ)) := by
    simp [hn.neg_pow]
    ring
  rw [hsub] at hmap
  exact (irreducible_isUnit_mul (isUnit_neg_one : IsUnit (-1 : ℚ[X]))).mp hmap

/-- In particular, absolute-parameter irreducibility is derived. -/
theorem irreducible_pure_binomial_abs
    (n : ℕ) (hn : Odd n) (k : ℤ)
    (hirr : Irreducible ((X : ℚ[X]) ^ n - C (k : ℚ))) :
    Irreducible ((X : ℚ[X]) ^ n - C ((|k| : ℤ) : ℚ)) := by
  by_cases hk : 0 ≤ k
  · simpa only [abs_of_nonneg hk] using hirr
  · simpa only [abs_of_neg (lt_of_not_ge hk)] using
      irreducible_pure_binomial_neg n hn k hirr

/-- A literal sign choice, with sign 1 at zero. For the final helper k != 0,
    so this is precisely the usual sign of k. -/
theorem exists_abs_sign (k : ℤ) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ s * |k| = k := by
  by_cases hk : 0 ≤ k
  · exact ⟨1, Or.inl rfl, by simp [abs_of_nonneg hk]⟩
  · exact ⟨-1, Or.inr rfl, by simp [abs_of_neg (lt_of_not_ge hk)]⟩

/-- Mapping an integer polynomial to Q does not change its evaluation
    in a Q-field. This is the explicit A-to-D coefficient interface. -/
theorem aeval_map_intCast_rat
    {L : Type u} [Field L] [Algebra ℚ L] (H : ℤ[X]) (t : L) :
    aeval t (H.map (Int.castRingHom ℚ)) = aeval t H := by
  symm
  exact Polynomial.aeval_eq_aeval_map
    (RingHom.ext_int ((algebraMap ℚ L).comp (Int.castRingHom ℚ))
      (algebraMap ℤ L)) H t

/-- The actual finite integer coefficient vector of a polynomial. -/
theorem aeval_int_eq_fin_sum
    (n : ℕ) (H : ℤ[X]) (hH : H.natDegree < n) (t : ℝ) :
    aeval t H = ∑ j : Fin n, (H.coeff j.val : ℝ) * t ^ j.val := by
  simpa [Algebra.smul_def, ← Fin.sum_univ_eq_sum_range] using
    (Polynomial.aeval_eq_sum_range' hH t)

/-- Absorb the sign of the real root into INTEGER coefficients.
    No rational-to-integer descent is hidden in this step. -/
theorem aeval_int_signed_eq_fin_sum
    (n : ℕ) (H : ℤ[X]) (hH : H.natDegree < n) (s : ℤ) (ρ : ℝ) :
    aeval ((s : ℝ) * ρ) H =
      ∑ j : Fin n, ((H.coeff j.val * s ^ j.val : ℤ) : ℝ) * ρ ^ j.val := by
  rw [aeval_int_eq_fin_sum n H hH]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Int.cast_mul, Int.cast_pow, mul_pow]
  ring

/-- Extend the checked finite-coefficient endpoint from A>0 to A!=0.
    In the negative branch negate every coefficient, A, and s. Since
    q>n>=5 and q is prime, q is odd and this negates the qth power. -/
theorem integral_power_order_exclusion_nonzero_A_fin
    (n q : ℕ) (hn : 5 ≤ n) (hq : q.Prime) (hnq : n < q)
    (k : ℤ) (hk : 1 < k) (ρ : ℝ) (hρ₀ : 0 < ρ)
    (hρpow : ρ ^ n = (k : ℝ))
    (hirr : Irreducible ((X : ℚ[X]) ^ n - C (k : ℚ)))
    (c : Fin n → ℤ) (A : ℤ) (hA : A ≠ 0)
    (s : ℤ) (hs : s = 1 ∨ s = -1) :
    (∑ j : Fin n, (c j : ℝ) * ρ ^ j.val) ^ q ≠
      (A : ℝ) - (s : ℝ) * ρ := by
  intro heq
  by_cases hApos : 0 < A
  · exact (PillaiIntegralPowerOrder.integral_power_order_exclusion_fin
      n q hn hq hnq k hk ρ hρ₀ hρpow hirr c A hApos s hs) heq
  · have hAneg : 0 < -A := by omega
    have hqodd : Odd q := hq.odd_of_ne_two (by omega)
    have hsneg : -s = 1 ∨ -s = -1 := by
      rcases hs with rfl | rfl <;> norm_num
    have hsum : (∑ j : Fin n, ((-c j : ℤ) : ℝ) * ρ ^ j.val) =
        -(∑ j : Fin n, (c j : ℝ) * ρ ^ j.val) := by
      simp only [Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
    have heqneg : (∑ j : Fin n, ((-c j : ℤ) : ℝ) * ρ ^ j.val) ^ q =
        ((-A : ℤ) : ℝ) - ((-s : ℤ) : ℝ) * ρ := by
      rw [hsum, hqodd.neg_pow, heq]
      simp only [Int.cast_neg]
      ring
    exact (PillaiIntegralPowerOrder.integral_power_order_exclusion_fin
      n q hn hq hnq k hk ρ hρ₀ hρpow hirr (fun j => -c j)
      (-A) hAneg (-s) hsneg) heqneg

/-- Signed k, signed nonzero A, and an arbitrary Q-field containing theta.

    The positive real root of |k| is constructed here. The equation at its
    signed version is propagated by the checked algebraic A theorem. The
    absolute-parameter irreducibility and all coefficient signs are proved
    in this file. Complex conjugate equations remain internal to the checked
    integral-power-order endpoint; they are not hypotheses of this helper.

    A != 0 and the actual integer polynomial are intentional input facts.
    The final global wrapper must supply them, so this theorem is NOT the
    final scoped irreducibility result. -/
theorem signed_integer_polynomial_affine_exclusion
    {L : Type u} [Field L] [Algebra ℚ L]
    (p q : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hq : q.Prime) (hpq : p < q)
    (k : ℤ) (hk : 1 < |k|)
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (A : ℤ) (hA : A ≠ 0) (θ : L) (hθ : θ ^ p = (k : L))
    (H : ℤ[X]) (hH : H.natDegree < p)
    (heq : (aeval θ H) ^ q = (A : L) - θ) : False := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hirrabs : Irreducible ((X : ℚ[X]) ^ p - C ((|k| : ℤ) : ℚ)) :=
    irreducible_pure_binomial_abs p hpodd k hirr
  have hkpos : (0 : ℤ) < |k| := lt_trans (by norm_num) hk
  have hkposR : (0 : ℝ) < ((|k| : ℤ) : ℝ) := by exact_mod_cast hkpos
  let ρ : ℝ := (((|k| : ℤ) : ℝ)) ^ ((p : ℝ)⁻¹)
  have hρ₀ : 0 < ρ := Real.rpow_pos_of_pos hkposR _
  have hρpow : ρ ^ p = ((|k| : ℤ) : ℝ) :=
    Real.rpow_inv_natCast_pow hkposR.le hp.ne_zero
  obtain ⟨s, hs, hsabs⟩ := exists_abs_sign k
  have hspow : (s : ℝ) ^ p = (s : ℝ) := by
    rcases hs with rfl | rfl
    · simp
    · simpa using (hpodd.neg_one_pow (α := ℝ))
  have ht : ((s : ℝ) * ρ) ^ p = (k : ℝ) := by
    rw [mul_pow, hspow, hρpow]
    exact_mod_cast hsabs
  have heqQ : (aeval θ (H.map (Int.castRingHom ℚ))) ^ q = (A : L) - θ := by
    simpa only [aeval_map_intCast_rat] using heq
  have heqR : (aeval ((s : ℝ) * ρ) H) ^ q =
      (A : ℝ) - (s : ℝ) * ρ := by
    have hprop := PillaiLocalCoefficients.power_equation_at_root
      p q k A θ hθ hirr (H.map (Int.castRingHom ℚ)) heqQ ((s : ℝ) * ρ) ht
    simpa only [aeval_map_intCast_rat] using hprop
  have hfin :
      (∑ j : Fin p, ((H.coeff j.val * s ^ j.val : ℤ) : ℝ) * ρ ^ j.val) ^ q =
        (A : ℝ) - (s : ℝ) * ρ := by
    rw [← aeval_int_signed_eq_fin_sum p H hH s ρ]
    exact heqR
  exact (integral_power_order_exclusion_nonzero_A_fin
    p q hp5 hq hpq |k| hk ρ hρ₀ hρpow hirrabs
    (fun j => H.coeff j.val * s ^ j.val) A hA s hs) hfin

/-- Variant matching a rational power-basis polynomial already represented
    as the coefficientwise image of H. It adds no new hypothesis. -/
theorem signed_mapped_integer_polynomial_affine_exclusion
    {L : Type u} [Field L] [Algebra ℚ L]
    (p q : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hq : q.Prime) (hpq : p < q)
    (k : ℤ) (hk : 1 < |k|)
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (A : ℤ) (hA : A ≠ 0) (θ : L) (hθ : θ ^ p = (k : L))
    (H : ℤ[X]) (hH : H.natDegree < p)
    (heq : (aeval θ (H.map (Int.castRingHom ℚ))) ^ q = (A : L) - θ) : False := by
  apply signed_integer_polynomial_affine_exclusion
    p q hp hp5 hq hpq k hk hirr A hA θ hθ H hH
  simpa only [aeval_map_intCast_rat] using heq

end PillaiSignedRealExclusion
