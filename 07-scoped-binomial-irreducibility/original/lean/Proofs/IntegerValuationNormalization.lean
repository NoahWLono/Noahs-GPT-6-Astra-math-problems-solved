import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Elementary arithmetic interface for the global coefficient assembly. -/
set_option autoImplicit false
namespace PillaiValuationNormalization

/-- Extract the exact integer unit factor at a rational prime. -/
theorem exists_integer_unit_factor
    (ell : ℕ) [Fact ell.Prime] (k : ℤ) (hk : k ≠ 0) :
    ∃ U : ℤ, k = (ell : ℤ) ^ padicValInt ell k * U ∧ ¬ (ell : ℤ) ∣ U := by
  obtain ⟨U, hU⟩ := padicValInt_dvd (p := ell) k
  refine ⟨U, hU, ?_⟩
  rintro ⟨v, hv⟩
  have hbad : (ell : ℤ) ^ (padicValInt ell k + 1) ∣ k := by
    refine ⟨v, ?_⟩
    calc
      k = (ell : ℤ) ^ padicValInt ell k * U := hU
      _ = (ell : ℤ) ^ padicValInt ell k * ((ell : ℤ) * v) := by rw [hv]
      _ = (ell : ℤ) ^ (padicValInt ell k + 1) * v := by
        rw [pow_succ, mul_assoc]
  rcases (padicValInt_dvd_iff (p := ell) (padicValInt ell k + 1) k).mp hbad with hzero | hle
  · exact hk hzero
  · omega

/-- A genuine parameter prime gives a positive exponent. -/
theorem valuation_pos_of_prime_dvd
    (ell : ℕ) [Fact ell.Prime] (k : ℤ) (hk : k ≠ 0)
    (hell : (ell : ℤ) ∣ k) : 0 < padicValInt ell k := by
  have hpow : (ell : ℤ) ^ 1 ∣ k := by simpa only [pow_one] using hell
  rcases (padicValInt_dvd_iff (p := ell) 1 k).mp hpow with hzero | hle
  · exact False.elim (hk hzero)
  · exact hle

/-- This supplies exactly the finite integer data for C1/C2. -/
theorem normalized_parameter_data
    (ell p : ℕ) [Fact ell.Prime] (k : ℤ) (hk : k ≠ 0)
    (hell : (ell : ℤ) ∣ k) (hsmall : padicValInt ell k < p) :
    ∃ r : ℕ, 0 < r ∧ r < p ∧
      ∃ U : ℤ, k = (ell : ℤ) ^ r * U ∧ ¬ (ell : ℤ) ∣ U := by
  obtain ⟨U, hU, hnot⟩ := exists_integer_unit_factor ell k hk
  exact ⟨padicValInt ell k, valuation_pos_of_prime_dvd ell k hk hell,
    hsmall, U, hU, hnot⟩

end PillaiValuationNormalization
