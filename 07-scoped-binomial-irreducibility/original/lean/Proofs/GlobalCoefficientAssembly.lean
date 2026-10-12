import ConcreteParameterCoefficients
import PadicCoefficientLift
import TraceDenominators
import RationalLocalIntersection
import IntegerValuationNormalization
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Nat.Prime.Int

/-!
# Natural global coefficient assembly

The actual B/C local lifts and trace denominator bounds give integer coefficients.
Only prime/valuation data, reducedness and the actual affine equation are inputs.
-/

set_option autoImplicit false

open Algebra Polynomial
open scoped BigOperators

noncomputable section

namespace PillaiGlobalCoefficients

universe u

lemma parameter_ne_zero (k : ℤ) (hkabs : 1 < k.natAbs) : k ≠ 0 := by
  intro hk
  simp [hk] at hkabs

/-- A nonunit integer has an actual positive rational prime divisor. -/
lemma exists_parameter_prime (k : ℤ) (hkabs : 1 < k.natAbs) :
    ∃ ell : ℕ, ell.Prime ∧ (ell : ℤ) ∣ k := by
  obtain ⟨ell, hell, hdvd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hkabs)
  exact ⟨ell, hell, Int.natCast_dvd.mpr hdvd⟩

/-- Natural irreducibility, independent of any affine equation. The valuation
hypotheses produce the normalization used by the actual C field construction. -/
theorem rational_binomial_irreducible_of_valuation_bounds
    (p : ℕ) (hp : p.Prime) (k : ℤ) (hkabs : 1 < k.natAbs)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p) :
    Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)) := by
  obtain ⟨ell, hell, hdvd⟩ := exists_parameter_prime k hkabs
  letI : Fact ell.Prime := ⟨hell⟩
  obtain ⟨r, hr0, hrp, U, hk, hU⟩ :=
    PillaiValuationNormalization.normalized_parameter_data ell p k
      (parameter_ne_zero k hkabs) hdvd (hval ell hell hdvd)
  exact PillaiLocalCoefficients.rational_binomial_irreducible_of_parameter_normalization
    ell p hp r hr0 hrp k U hk hU

/-- Turn coefficientwise integer representatives into a literal polynomial,
with the degree bound preserved even for the zero polynomial. -/
theorem integer_polynomial_of_coefficients
    (p : ℕ) (hp : 1 ≤ p) (G : ℚ[X]) (hG : G.natDegree < p)
    (hc : ∀ j : Fin p, ∃ z : ℤ, (z : ℚ) = G.coeff j.val) :
    ∃ H : ℤ[X], H.natDegree < p ∧ H.map (Int.castRingHom ℚ) = G := by
  classical
  choose z hz using hc
  refine ⟨Polynomial.ofFn p z, Polynomial.ofFn_natDegree_lt hp z, ?_⟩
  ext j
  rw [coeff_map]
  by_cases hj : j < p
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt z hj]
    exact hz ⟨j, hj⟩
  · have hpj : p ≤ j := Nat.le_of_not_gt hj
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge z hpj, map_zero]
    exact (coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hG hpj)).symm

/-- Integrality is derived from the two power equations, then fed to the actual
trace theorem after expressing evaluation as the finite coefficient sum. -/
theorem denominator_bounds_of_power_equation
    (p q : ℕ) (hp : 1 ≤ p) (hq : 0 < q) (k A : ℤ)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ) :
    ((G.coeff 0).den : ℤ) ∣ (p : ℤ) ∧
      ∀ j : Fin p, 0 < j.val → ((G.coeff j.val).den : ℤ) ∣ (p : ℤ) * k := by
  have hθInt : IsIntegral ℤ θ := by
    apply IsIntegral.of_pow (show 0 < p by omega)
    rw [hθ]
    exact isIntegral_intCast k
  have hγInt : IsIntegral ℤ (aeval θ G) :=
    PillaiLocalCoefficients.isIntegral_of_integer_power_equation
      q hq A (aeval θ G) θ hθInt heq
  have hsum : (∑ j : Fin p, (G.coeff j.val : L) * θ ^ j.val) = aeval θ G := by
    rw [aeval_eq_sum_range' hG θ, Finset.sum_range]
    simp only [Algebra.smul_def, eq_ratCast]
  exact PillaiTrace.irreducible_denominator_dvd p hp k θ hθ hirr
    (fun j : Fin p => G.coeff j.val) (by rw [hsum]; exact hγInt)

/-- Natural C2: the exponent prime cannot divide the parameter in an actual
power equation. Normalization and global irreducibility are both derived. -/
theorem exponent_prime_not_dvd_parameter
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (k A : ℤ) (hkabs : 1 < k.natAbs)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (G : ℚ[X]) (heq : (aeval θ G) ^ q = (A : L) - θ) :
    ¬ (q : ℤ) ∣ k := by
  intro hqk
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨r, hr0, hrp, U, hk, hU⟩ :=
    PillaiValuationNormalization.normalized_parameter_data q p k
      (parameter_ne_zero k hkabs) hqk (hval q hq hqk)
  exact PillaiLocalCoefficients.no_normalized_power_equation_at_exponent_parameter
    p q hp hpq r hr0 hrp k U A hk hU θ hθ G heq

/-- Natural C1 at each parameter prime. The separate case ell = q is discharged
by natural C2, so the caller supplies neither a normalization nor ell ≠ q. -/
theorem parameter_prime_coefficients_of_valuation_bounds
    (ell p q : ℕ) [Fact ell.Prime]
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (k A : ℤ) (hkabs : 1 < k.natAbs)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p)
    (hellk : (ell : ℤ) ∣ k)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ) :
    (¬ (ell : ℤ) ∣ A) ∧
      ∀ j : ℕ, ∃ z : ℤ_[ell],
        algebraMap ℤ_[ell] ℚ_[ell] z = (G.coeff j : ℚ_[ell]) := by
  have hqk := exponent_prime_not_dvd_parameter p q hp hq hpq
    k A hkabs hval θ hθ G heq
  have hellq : ell ≠ q := by
    intro he
    apply hqk
    simpa only [he] using hellk
  obtain ⟨r, hr0, hrp, U, hk, hU⟩ :=
    PillaiValuationNormalization.normalized_parameter_data ell p k
      (parameter_ne_zero k hkabs) hellk (hval ell Fact.out hellk)
  exact PillaiLocalCoefficients.parameter_prime_coefficients_of_normalized_power_equation
    ell p q hp hq hpq hellq r hr0 hrp k U A hk hU θ hθ G hG heq

/-- The scalar in the actual affine equation is nonzero. This follows from the
unit conclusion at any prime divisor of the nonunit parameter. -/
theorem scalar_ne_zero_of_power_equation
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (k A : ℤ) (hkabs : 1 < k.natAbs)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ) : A ≠ 0 := by
  obtain ⟨ell, hell, hellk⟩ := exists_parameter_prime k hkabs
  letI : Fact ell.Prime := ⟨hell⟩
  have hA := (parameter_prime_coefficients_of_valuation_bounds ell p q hp hq hpq
    k A hkabs hval hellk θ hθ G hG heq).1
  intro hzero
  exact hA (by simp [hzero])

/-- Every possible denominator prime supplied by the trace bound is excluded
by an actual integral local lift: C at primes of k, B at p when p ∤ k. -/
theorem support_prime_not_dvd_coefficient_denominator
    (p q : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hq : q.Prime) (hpq : p < q)
    (k A : ℤ) (hkabs : 1 < k.natAbs)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ)
    (ell : ℕ) (hell : ell.Prime) (hsupport : ell = p ∨ (ell : ℤ) ∣ k)
    (j : ℕ) : ¬ ell ∣ (G.coeff j).den := by
  letI : Fact ell.Prime := ⟨hell⟩
  by_cases hellk : (ell : ℤ) ∣ k
  · obtain ⟨z, hz⟩ := (parameter_prime_coefficients_of_valuation_bounds
      ell p q hp hq hpq k A hkabs hval hellk θ hθ G hG heq).2 j
    exact PillaiRationalIntersection.prime_not_dvd_den_of_padic_lift ell (G.coeff j) z hz
  · have hellp : ell = p := hsupport.resolve_right hellk
    subst ell
    have hirr := rational_binomial_irreducible_of_valuation_bounds p hp k hkabs hval
    obtain ⟨z, hz⟩ := PillaiLocalCoefficients.padic_coefficients_of_power_equation
      p q hp3 hq hpq k A hellk θ hθ hirr G hG heq j
    exact PillaiRationalIntersection.prime_not_dvd_den_of_padic_lift p (G.coeff j) z hz

/-- Natural global integer coefficients in the reduced rational representative.
There are no assumed local integrality, normalization, irreducibility, trace,
denominator-exclusion or coordinate-uniqueness bridges. -/
theorem integer_coefficients_of_power_equation
    (p q : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hq : q.Prime) (hpq : p < q)
    (k A : ℤ) (hkabs : 1 < k.natAbs)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ) :
    ∀ j : Fin p, ∃ z : ℤ, (z : ℚ) = G.coeff j.val := by
  have hirr := rational_binomial_irreducible_of_valuation_bounds p hp k hkabs hval
  obtain ⟨hden0, hden⟩ := denominator_bounds_of_power_equation
    p q (by omega) hq.pos k A θ hθ hirr G hG heq
  intro j
  by_cases hj0 : j.val = 0
  · rw [hj0]
    apply PillaiRationalIntersection.exists_integer_of_denominator_support
      (G.coeff 0) (p : ℤ) hden0
    intro ell hell helldvd
    have hellp : ell = p :=
      ((hp.dvd_iff_eq hell.ne_one).mp (Int.natCast_dvd_natCast.mp helldvd)).symm
    exact support_prime_not_dvd_coefficient_denominator p q hp hp3 hq hpq
      k A hkabs hval θ hθ G hG heq ell hell (Or.inl hellp) 0
  · apply PillaiRationalIntersection.exists_integer_of_denominator_support
      (G.coeff j.val) ((p : ℤ) * k) (hden j (Nat.pos_of_ne_zero hj0))
    intro ell hell helldvd
    have hsupport : ell = p ∨ (ell : ℤ) ∣ k := by
      rcases (Nat.prime_iff_prime_int.mp hell).dvd_or_dvd helldvd with hellp | hellk
      · exact Or.inl ((hp.dvd_iff_eq hell.ne_one).mp
          (Int.natCast_dvd_natCast.mp hellp)).symm
      · exact Or.inr hellk
    exact support_prime_not_dvd_coefficient_denominator p q hp hp3 hq hpq
      k A hkabs hval θ hθ G hG heq ell hell hsupport j.val

/-- Final natural endpoint: A is nonzero and the reduced rational polynomial
is literally the rational image of a reduced integer polynomial. -/
theorem integer_polynomial_of_power_equation
    (p q : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hq : q.Prime) (hpq : p < q)
    (k A : ℤ) (hkabs : 1 < k.natAbs)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ) :
    A ≠ 0 ∧ ∃ H : ℤ[X], H.natDegree < p ∧ H.map (Int.castRingHom ℚ) = G := by
  refine ⟨scalar_ne_zero_of_power_equation p q hp hq hpq
    k A hkabs hval θ hθ G hG heq, ?_⟩
  apply integer_polynomial_of_coefficients p (by omega) G hG
  exact integer_coefficients_of_power_equation p q hp hp3 hq hpq
    k A hkabs hval θ hθ G hG heq

end PillaiGlobalCoefficients
