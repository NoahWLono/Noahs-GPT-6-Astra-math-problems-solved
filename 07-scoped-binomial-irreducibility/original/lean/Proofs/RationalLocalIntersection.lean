import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Data.Nat.Prime.Basic

/-! Elementary arithmetic interface for the global coefficient assembly. -/
set_option autoImplicit false
namespace PillaiRationalIntersection

/-- An actual integral p-adic lift excludes p from the reduced denominator. -/
theorem prime_not_dvd_den_of_padic_lift
    (ell : ℕ) [Fact ell.Prime] (r : ℚ)
    (a : ℤ_[ell]) (ha : algebraMap ℤ_[ell] ℚ_[ell] a = (r : ℚ_[ell])) :
    ¬ ell ∣ r.den := by
  have hnorm : ‖(r : ℚ_[ell])‖ ≤ 1 := by
    rw [← ha, PadicInt.algebraMap_apply]
    exact a.property
  have hu : IsUnit (r.den : ℤ_[ell]) := PadicInt.isUnit_den r hnorm
  intro hd
  have hn : ‖(r.den : ℤ_[ell])‖ < 1 := PadicInt.norm_natCast_lt_one_iff.mpr hd
  exact (PadicInt.not_isUnit_iff.mpr hn) hu

/-- A finite denominator-support bound and exclusion of its supporting primes
suffice for a literal integer representative. The exclusions must be proved by
actual B/C local lifts before this lemma is used in the final wrapper. -/
theorem exists_integer_of_denominator_support
    (r : ℚ) (d : ℤ) (hd : (r.den : ℤ) ∣ d)
    (hexclude : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ d → ¬ ell ∣ r.den) :
    ∃ z : ℤ, (z : ℚ) = r := by
  have hden : r.den = 1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro ell hp hell
    have hell' : (ell : ℤ) ∣ (r.den : ℤ) := by exact_mod_cast hell
    exact hexclude ell hp (hell'.trans hd) hell
  exact ⟨r.num, (Rat.den_eq_one_iff r).mp hden⟩

end PillaiRationalIntersection
