import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

namespace ProgressivePool

/-- A kernel-checked upper bound avoids evaluating a huge binomial recursively. -/
theorem choose_tail_certificate :
    Nat.choose (33554432 + 64) 33 * 2^286 <
      (1073741789 - 33554432 - 64)^33 := by
  have hb : Nat.factorial 33 * Nat.choose (33554432+64) 33 ≤
      (33554432+64)^33 := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ _
  have hn : (33554432+64)^33 * 2^286 <
      Nat.factorial 33 * (1073741789-33554432-64)^33 := by
    norm_num [Nat.factorial]
  have hh := (Nat.mul_le_mul_right (2^286) hb).trans_lt hn
  rw [Nat.mul_assoc] at hh
  exact Nat.lt_of_mul_lt_mul_left hh

/-- Same global query budget, including the designated final invocation. -/
theorem terminal_seven_certificate :
    (2^64+1) * 2^145 < (1073741789 : ℕ)^7 := by norm_num

theorem schedule_share_certificate :
    (64 * 1024 * 61852 : ℕ) = 262144 * 15463 := by norm_num

theorem pool_storage_certificate :
    (1024*61852 + 2*64*(1024+61852) : ℕ) = 71384576 := by norm_num

#print axioms choose_tail_certificate
#print axioms terminal_seven_certificate
end ProgressivePool
