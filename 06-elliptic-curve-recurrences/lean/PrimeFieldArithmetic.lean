import Mathlib.Data.Nat.Prime.Basic

/-! Pure arithmetic used in T5. The Hasse-derived lower bound is explicit;
this file does not claim to prove Hasse's theorem for elliptic curves. -/
namespace Astra01

theorem prime_field_divisibility_excluded (p n : ℕ) (hp : p.Prime) (hn : n.Prime)
    (hp17 : 17 ≤ p) (hlower : p+1 < 2*n) :
    ¬ n ∣ p-1 ∧ ¬ n ∣ p+1 := by
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  constructor
  · intro hdvd
    have heq : p-1 = n := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd (by omega)
    have hnodd := hn.eq_two_or_odd
    omega
  · intro hdvd
    have heq : p+1 = n := Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd hlower
    have hnodd := hn.eq_two_or_odd
    omega

#print axioms prime_field_divisibility_excluded
end Astra01
