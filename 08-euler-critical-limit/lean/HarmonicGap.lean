import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Elementary uniform bounds for the final `j` terms of a harmonic number.
The estimates are valid up to `j = n`, not merely for fixed `j` or a short tail.
-/

open scoped BigOperators

noncomputable section

namespace EulerScalingAnalytic

/-- Appending one term to a reversed harmonic tail. -/
lemma harmonic_gap_succ (n j : ℕ) (hj : j < n) :
    (harmonic n : ℝ) - harmonic (n - (j + 1)) =
      ((harmonic n : ℝ) - harmonic (n - j)) + ((n - j : ℕ) : ℝ)⁻¹ := by
  have hs : n - (j + 1) + 1 = n - j := by omega
  have h := congrArg (fun q : ℚ => (q : ℝ)) (harmonic_succ (n - (j + 1)))
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, hs] at h
  linarith

/-- A harmonic gap is exactly a sum of descending reciprocals. -/
lemma harmonic_gap_eq_sum (n j : ℕ) (hj : j ≤ n) :
    (harmonic n : ℝ) - harmonic (n - j) =
      ∑ r ∈ Finset.range j, ((n - r : ℕ) : ℝ)⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [harmonic_gap_succ n j (by omega), ih (by omega), Finset.sum_range_succ]

lemma harmonic_gap_nonneg (n j : ℕ) (hj : j ≤ n) :
    0 ≤ (harmonic n : ℝ) - harmonic (n - j) := by
  rw [harmonic_gap_eq_sum n j hj]
  exact Finset.sum_nonneg (fun r _ => inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The denominator of each reciprocal compensates for its distance from the endpoint. -/
lemma harmonic_gap_reciprocal_le (n r : ℕ) (hr : r < n) :
    ((n - r : ℕ) : ℝ)⁻¹ ≤ ((r : ℝ) + 1) / (n : ℝ) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd : 0 < ((n - r : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hnat : n ≤ (r + 1) * (n - r) := by
    have hpos : 1 ≤ n - r := by omega
    have hmul := Nat.mul_le_mul_left r hpos
    have hsum : n = (n - r) + r := by omega
    nlinarith
  rw [← one_div]
  apply (div_le_div_iff₀ hd hn).2
  simpa only [one_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    (show (n : ℝ) ≤ (((r + 1) * (n - r) : ℕ) : ℝ) by exact_mod_cast hnat)

/-- A uniform quadratic bound, including the full gap `j = n`. -/
theorem harmonic_gap_le_sq_div (n j : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) :
    (harmonic n : ℝ) - harmonic (n - j) ≤ (j : ℝ) ^ 2 / (n : ℝ) := by
  have hn0 : 0 ≤ (n : ℝ) := (Nat.cast_pos.mpr (Nat.succ_le_iff.mp hn)).le
  induction j with
  | zero => simp
  | succ j ih =>
      have hjn : j < n := by omega
      rw [harmonic_gap_succ n j hjn]
      calc
        ((harmonic n : ℝ) - harmonic (n - j)) + ((n - j : ℕ) : ℝ)⁻¹
            ≤ (j : ℝ) ^ 2 / (n : ℝ) + ((j : ℝ) + 1) / (n : ℝ) :=
          add_le_add (ih (by omega)) (harmonic_gap_reciprocal_le n j hjn)
        _ = ((j : ℝ) ^ 2 + ((j : ℝ) + 1)) / (n : ℝ) := (add_div _ _ _).symm
        _ ≤ ((j + 1 : ℕ) : ℝ) ^ 2 / (n : ℝ) := by
          apply div_le_div_of_nonneg_right _ hn0
          simp only [Nat.cast_add, Nat.cast_one]
          nlinarith [Nat.cast_nonneg (α := ℝ) j]

/-- The two-sided bound used for uniform domination in critical scaling. -/
theorem harmonic_gap_bounds (n j : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) :
    0 ≤ (harmonic n : ℝ) - harmonic (n - j) ∧
      (harmonic n : ℝ) - harmonic (n - j) ≤ (j : ℝ) ^ 2 / (n : ℝ) :=
  ⟨harmonic_gap_nonneg n j hj, harmonic_gap_le_sq_div n j hn hj⟩

/-- Moving a fixed-length gap to a later harmonic number only decreases it. -/
lemma harmonic_gap_antitone (n m j : ℕ) (hj : j ≤ n) (hnm : n ≤ m) :
    (harmonic m : ℝ) - harmonic (m - j) ≤
      (harmonic n : ℝ) - harmonic (n - j) := by
  rw [harmonic_gap_eq_sum m j (hj.trans hnm), harmonic_gap_eq_sum n j hj]
  apply Finset.sum_le_sum
  intro r hr
  have hrn : r < n := (Finset.mem_range.mp hr).trans_le hj
  apply inv_anti₀ (Nat.cast_pos.mpr (show 0 < n - r by omega))
  exact_mod_cast (Nat.sub_le_sub_right hnm r)

lemma harmonic_gap_double_le (n j : ℕ) (hj : j ≤ n) :
    (harmonic (2 * n) : ℝ) - harmonic (2 * n - j) ≤
      (harmonic n : ℝ) - harmonic (n - j) :=
  harmonic_gap_antitone n (2 * n) j hj (by omega)

#print axioms harmonic_gap_bounds
#print axioms harmonic_gap_double_le

end EulerScalingAnalytic
