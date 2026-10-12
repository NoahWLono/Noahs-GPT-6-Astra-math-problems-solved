import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Exact finite endpoint weights for the Euler approximant.

The weights are defined by their original binomial/factorial expression. The
finite product formula is derived from the adjacent binomial identities and
factorial recurrence; it is not part of the definition.
-/

noncomputable section

namespace EulerScalingAnalytic

open scoped BigOperators

/-- The original binomial/factorial weight. -/
def weight (n p k : ℕ) : ℝ :=
  ((Nat.choose n k : ℝ) ^ 2 * (Nat.choose (n + k) k : ℝ) ^ p) /
    (Nat.factorial k : ℝ)

/-- The endpoint scaling parameter. -/
def scale (n p : ℕ) : ℝ := (n : ℝ) ^ 3 / (2 : ℝ) ^ p

/-- Endpoint weights, extended by zero outside their finite support. -/
def endpoint (n p j : ℕ) : ℝ :=
  if j ≤ n then weight n p (n - j) / weight n p n else 0

theorem weight_pos (n p k : ℕ) (hk : k ≤ n) : 0 < weight n p k := by
  have h₁ : 0 < (Nat.choose n k : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hk)
  have h₂ : 0 < (Nat.choose (n + k) k : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have h₃ : 0 < (Nat.factorial k : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos k)
  unfold weight
  positivity

theorem weight_endpoint_pos (n p : ℕ) : 0 < weight n p n :=
  weight_pos n p n le_rfl

/-- Adjacent first binomial coefficients, as an equality in the reals. -/
private theorem choose_down (n k : ℕ) (hk : k < n) :
    (Nat.choose n k : ℝ) =
      (Nat.choose n (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) /
        ((n - k : ℕ) : ℝ) := by
  have hd : ((n - k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_of_lt hk)
  apply (eq_div_iff hd).2
  have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq n k)
  simpa only [Nat.cast_mul] using h.symm

/-- Adjacent diagonal binomial coefficients, as an equality in the reals. -/
private theorem choose_diagonal_down (n k : ℕ) :
    (Nat.choose (n + k) k : ℝ) =
      (Nat.choose (n + (k + 1)) (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) /
        ((n + k + 1 : ℕ) : ℝ) := by
  have hd : ((n + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hd).2
  have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.add_one_mul_choose_eq (n + k) k)
  simpa only [Nat.cast_mul, Nat.add_assoc, mul_comm] using h

/-- The descending recurrence follows directly from the original weights. -/
theorem weight_adjacent (n p k : ℕ) (hk : k < n) :
    weight n p k = weight n p (k + 1) *
      (((k + 1 : ℕ) : ℝ) ^ 3 / ((n - k : ℕ) : ℝ) ^ 2 *
        (((k + 1 : ℕ) : ℝ) / ((n + k + 1 : ℕ) : ℝ)) ^ p) := by
  have h₁ : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h₂ : ((n - k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_of_lt hk)
  have h₃ : ((n + k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h₄ : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  unfold weight
  rw [choose_down n k hk, choose_diagonal_down n k]
  simp only [Nat.factorial_succ, Nat.cast_mul, mul_pow, div_pow]
  field_simp [h₁, h₂, h₃, h₄]

/-- Descending the weight index is ascending the endpoint index. -/
theorem endpoint_adjacent (n p j : ℕ) (hj : j + 1 ≤ n) :
    endpoint n p (j + 1) = endpoint n p j *
      (((n - j : ℕ) : ℝ) ^ 3 / ((j + 1 : ℕ) : ℝ) ^ 2 *
        (((n - j : ℕ) : ℝ) / ((2 * n - j : ℕ) : ℝ)) ^ p) := by
  have hj' : j ≤ n := by omega
  have hk : n - (j + 1) < n := by omega
  have h₁ : n - (j + 1) + 1 = n - j := by omega
  have h₂ : n - (n - (j + 1)) = j + 1 := by omega
  have h₃ : n + (n - (j + 1)) + 1 = 2 * n - j := by omega
  have h := weight_adjacent n p (n - (j + 1)) hk
  rw [h₁, h₂, h₃] at h
  simp only [endpoint, if_pos hj, if_pos hj']
  rw [h]
  ring

/-- Rewrite a single adjacent ratio in scaled endpoint coordinates. -/
private theorem adjacent_eq_scaled (n p j : ℕ) (hn : 0 < n) (hj : j < n) :
    (((n - j : ℕ) : ℝ) ^ 3 / ((j + 1 : ℕ) : ℝ) ^ 2 *
      (((n - j : ℕ) : ℝ) / ((2 * n - j : ℕ) : ℝ)) ^ p) =
    scale n p / ((j + 1 : ℕ) : ℝ) ^ 2 *
      ((1 - (j : ℝ) / (n : ℝ)) ^ 3 *
        ((1 - (j : ℝ) / (n : ℝ)) /
          (1 - (j : ℝ) / (2 * (n : ℝ)))) ^ p) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hjR : (j : ℝ) < n := by exact_mod_cast hj
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hden : 2 * (n : ℝ) - j ≠ 0 := by linarith
  have hk : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hc₁ : ((n - j : ℕ) : ℝ) = (n : ℝ) - j :=
    Nat.cast_sub (Nat.le_of_lt hj)
  have hc₂ : ((2 * n - j : ℕ) : ℝ) = 2 * (n : ℝ) - j := by
    rw [Nat.cast_sub (by omega : j ≤ 2 * n)]
    norm_num
  have ha : 1 - (j : ℝ) / n = ((n : ℝ) - j) / n := by
    field_simp
  have hb : 1 - (j : ℝ) / (2 * (n : ℝ)) =
      (2 * (n : ℝ) - j) / (2 * (n : ℝ)) := by
    field_simp
  have hc : (1 - (j : ℝ) / n) / (1 - (j : ℝ) / (2 * (n : ℝ))) =
      2 * (((n : ℝ) - j) / (2 * (n : ℝ) - j)) := by
    rw [ha, hb]
    field_simp
  rw [hc₁, hc₂, hc, ha]
  unfold scale
  simp only [mul_pow, div_pow]
  field_simp [hn0, hden, hk]

/-- The exact finite endpoint product, derived without an identity hypothesis. -/
theorem endpoint_eq_product (n p j : ℕ) (hn : 1 ≤ n) (hj : j ≤ n) :
    endpoint n p j =
      scale n p ^ j / (Nat.factorial j : ℝ) ^ 2 *
        ∏ r ∈ Finset.range j,
          ((1 - (r : ℝ) / (n : ℝ)) ^ 3 *
            ((1 - (r : ℝ) / (n : ℝ)) /
              (1 - (r : ℝ) / (2 * (n : ℝ)))) ^ p) := by
  induction j with
  | zero =>
      have hw : weight n p n ≠ 0 := ne_of_gt (weight_endpoint_pos n p)
      simp [endpoint, hw]
  | succ j ih =>
      have hj' : j < n := by omega
      rw [endpoint_adjacent n p j hj, adjacent_eq_scaled n p j (by omega) hj',
        ih (Nat.le_of_lt hj'), Finset.prod_range_succ]
      simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, mul_pow,
        div_eq_mul_inv, mul_inv_rev]
      ring

#print axioms weight_endpoint_pos
#print axioms endpoint_eq_product

end EulerScalingAnalytic
