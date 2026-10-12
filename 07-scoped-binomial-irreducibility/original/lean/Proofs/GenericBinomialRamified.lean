import GenericBinomialResidue
import Mathlib.Algebra.CharP.Lemmas

/-! The actual affine prime-power equation is impossible when the scalar prime
is a nonunit and at least the monic binomial degree. The integral binomial
identity proves the residue-characteristic step without adding a quotient
field, reducedness, or coordinate-uniqueness assumption. -/
set_option autoImplicit false
open Polynomial
namespace PillaiParameterC
universe u
variable {D : Type u} [CommRing D] [Nontrivial D]

/-- Generic ramified-exponent exclusion in the actual monic quotient. -/
theorem no_affine_prime_power_at_parameter
    (q n r : ℕ) (hq : q.Prime) (hnq : n ≤ q)
    (hqunit : ¬ IsUnit (q : D)) (hr : 0 < r) (hrn : r < n)
    (v c A : D) (hc : IsUnit c) (x : Order (q : D) v n)
    (hroot : x ^ q = scalar (q : D) v n A -
      scalar (q : D) v n c * tau (q : D) v n ^ r) : False := by
  obtain ⟨a, w, hx⟩ := exists_scalar_add_tau_mul (q : D) v n x
  have hdivn : scalar (q : D) v n (q : D) ∣ tau (q : D) v n ^ n := by
    rw [tau_pow, map_mul]
    exact dvd_mul_right _ _
  have hdivq : scalar (q : D) v n (q : D) ∣ tau (q : D) v n ^ q :=
    hdivn.trans (pow_dvd_pow _ hnq)
  have hfirst : scalar (q : D) v n (q : D) ∣ (tau (q : D) v n * w) ^ q := by
    rw [mul_pow]
    exact dvd_mul_of_dvd_left hdivq _
  have hsecond : scalar (q : D) v n (q : D) ∣
      (q : Order (q : D) v n) * (tau (q : D) v n * w) := by
    rw [map_natCast]
    exact dvd_mul_right _ _
  have hdiv : scalar (q : D) v n (q : D) ∣
      x ^ q - scalar (q : D) v n (a ^ q) := by
    have h := hq.dvd_add_pow_sub_pow_of_dvd
      (x := tau (q : D) v n * w) (y := scalar (q : D) v n a) hfirst hsecond
    simpa only [hx, map_pow, add_comm] using h
  apply scalar_ell_not_dvd_unit_monomial_sub_scalar (q : D) v hqunit hr hrn c (A - a ^ q) hc
  have hneg := dvd_neg.mpr hdiv
  convert hneg using 1
  rw [hroot, map_sub]
  ring

end PillaiParameterC
