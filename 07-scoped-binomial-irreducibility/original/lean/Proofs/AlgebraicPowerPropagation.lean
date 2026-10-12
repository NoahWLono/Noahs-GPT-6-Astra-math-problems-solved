import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Algebraic propagation of the affine power equation

Elaborated with Lean 4.32.2 at mathlib pin
905b95818eb32af7874a58b427f50c1711a5e96c. See the adjacent verification records
for source hashes, exact endpoints, resource guards, and checking limitations.
This source is outside every sealed handoff.

This module deliberately imports neither analytic Pillai modules nor p-adic modules.
It does not require a global-to-local embedding. Each destination root is an actual
element of its own Q-algebra field. The final integrality lemma needs only a
commutative base ring, so it applies to every local DVR used in the arithmetic.
-/

set_option autoImplicit false

open Polynomial

namespace PillaiLocalCoefficients

universe u v w

/-- the actual rational minimal polynomial is the supplied binomial.
Even positivity of the exponent is derived from irreducibility. -/
theorem pure_binomial_eq_minpoly
    {L : Type u} [Field L] [Algebra ℚ L]
    (p : ℕ) (k : ℤ) (θ : L)
    (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ))) :
    (X : ℚ[X]) ^ p - C (k : ℚ) = minpoly ℚ θ := by
  have hp : p ≠ 0 := by
    intro hp
    apply Polynomial.not_irreducible_C (1 - (k : ℚ))
    simpa only [hp, pow_zero, map_sub, map_one] using hirr
  apply minpoly.eq_of_irreducible_of_monic hirr
  · simp only [map_sub, map_pow, aeval_X, map_intCast, hθ, sub_self]
  · exact monic_X_pow_sub_C (k : ℚ) hp

/-- the equation at θ gives literal polynomial divisibility over Q. -/
theorem pure_binomial_dvd_power_relation
    {L : Type u} [Field L] [Algebra ℚ L]
    (p q : ℕ) (k A : ℤ) (θ : L)
    (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (heq : (aeval θ G) ^ q = (A : L) - θ) :
    (X : ℚ[X]) ^ p - C (k : ℚ) ∣ G ^ q - C (A : ℚ) + X := by
  rw [pure_binomial_eq_minpoly p k θ hθ hirr]
  apply minpoly.dvd ℚ θ
  simp only [map_add, map_sub, map_pow, aeval_X, map_intCast]
  simp [heq, sub_eq_add_neg, add_assoc, add_comm]

/-- evaluate the divisibility at any actual root in a Q-field. -/
theorem power_equation_at_root_of_dvd
    {E : Type v} [Field E] [Algebra ℚ E]
    (p q : ℕ) (k A : ℤ) (G : ℚ[X])
    (hdvd : (X : ℚ[X]) ^ p - C (k : ℚ) ∣ G ^ q - C (A : ℚ) + X)
    (t : E) (ht : t ^ p = (k : E)) :
    (aeval t G) ^ q = (A : E) - t := by
  have hroot : aeval t ((X : ℚ[X]) ^ p - C (k : ℚ)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_intCast, ht, sub_self]
  have hzero : aeval t (G ^ q - C (A : ℚ) + X) = 0 := by
    obtain ⟨Q, hQ⟩ := hdvd
    rw [hQ, map_mul, hroot, zero_mul]
  simp only [map_add, map_sub, map_pow, aeval_X, map_intCast] at hzero
  apply eq_sub_iff_add_eq.mpr
  apply sub_eq_zero.mp
  simpa only [sub_add_eq_add_sub] using hzero

/-- equation propagation, without a field embedding hypothesis. -/
theorem power_equation_at_root
    {L : Type u} [Field L] [Algebra ℚ L]
    {E : Type v} [Field E] [Algebra ℚ E]
    (p q : ℕ) (k A : ℤ) (θ : L)
    (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (heq : (aeval θ G) ^ q = (A : L) - θ)
    (t : E) (ht : t ^ p = (k : E)) :
    (aeval t G) ^ q = (A : E) - t := by
  exact power_equation_at_root_of_dvd p q k A G
    (pure_binomial_dvd_power_relation p q k A θ hθ hirr G heq) t ht

/-- integer affine power equations produce integrality over any
commutative base ring; the local DVR case is a specialization. -/
theorem isIntegral_of_integer_power_equation
    {R : Type w} [CommRing R]
    {E : Type v} [CommRing E] [Algebra R E]
    (q : ℕ) (hq : 0 < q) (A : ℤ) (x t : E)
    (ht : IsIntegral R t) (heq : x ^ q = (A : E) - t) :
    IsIntegral R x := by
  have hA : IsIntegral R (A : E) := by
    simpa only [map_intCast] using
      (isIntegral_algebraMap : IsIntegral R (algebraMap R E (A : R)))
  apply IsIntegral.of_pow hq
  rw [heq]
  exact hA.sub ht

/-- propagate and derive local integrality in one application. -/
theorem propagated_aeval_isIntegral
    {L : Type u} [Field L] [Algebra ℚ L]
    {R : Type w} [CommRing R]
    {E : Type v} [Field E] [Algebra ℚ E] [Algebra R E]
    (p q : ℕ) (hq : 0 < q) (k A : ℤ) (θ : L)
    (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (heq : (aeval θ G) ^ q = (A : L) - θ)
    (t : E) (ht : t ^ p = (k : E)) (htInt : IsIntegral R t) :
    IsIntegral R (aeval t G) := by
  exact isIntegral_of_integer_power_equation q hq A (aeval t G) t htInt
    (power_equation_at_root p q k A θ hθ hirr G heq t ht)

end PillaiLocalCoefficients
