import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.GCDMonoid.Nat

/-! The arithmetic extension-degree consequence in T4. The alternatives
q^k ≡ ±1 (mod n) are explicit inputs, not an assumed field classification. -/
namespace Astra01

theorem order_dvd_twice_extension (n q k : ℕ) (hq : 0 < q)
    (h : n ∣ q^k-1 ∨ n ∣ q^k+1) : orderOf (q : ZMod n) ∣ 2*k := by
  have hpow : (q : ZMod n)^k = 1 ∨ (q : ZMod n)^k = -1 := by
    rcases h with hm | hp
    · left
      have hz := (ZMod.natCast_eq_zero_iff (q^k-1) n).mpr hm
      rw [Nat.cast_sub (Nat.one_le_pow k q hq), Nat.cast_pow, Nat.cast_one] at hz
      exact sub_eq_zero.mp hz
    · right
      have hz := (ZMod.natCast_eq_zero_iff (q^k+1) n).mpr hp
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hz
      exact eq_neg_of_add_eq_zero_left hz
  apply orderOf_dvd_of_pow_eq_one
  rw [Nat.mul_comm 2 k, pow_mul]
  rcases hpow with hm | hp
  · rw [hm, one_pow]
  · rw [hp, neg_one_sq]

/-- The exact arithmetic equivalence stated in the manuscript. -/
theorem extension_divisibility_iff (e k : ℕ) :
    e / Nat.gcd e 2 ∣ k ↔ e ∣ 2*k := by
  rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left e 2) (Nat.gcd_pos_of_pos_right e (by decide))]
  exact dvd_gcd_mul_iff_dvd_mul

theorem minimal_extension_degree_divides (n q k : ℕ) (hq : 0 < q)
    (h : n ∣ q^k-1 ∨ n ∣ q^k+1) :
    orderOf (q : ZMod n) / Nat.gcd (orderOf (q : ZMod n)) 2 ∣ k :=
  (extension_divisibility_iff _ _).mpr (order_dvd_twice_extension n q k hq h)

#print axioms order_dvd_twice_extension
#print axioms extension_divisibility_iff
#print axioms minimal_extension_degree_divides
end Astra01
