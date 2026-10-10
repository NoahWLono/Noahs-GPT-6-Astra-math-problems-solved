import FreshSampling
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Exact confidence and work accounting.  Preparation counters certify the
amount of scheduled work, not the semantic correctness of matrix preparation. -/
namespace ProgressivePool.CostAndConfidence

def gamma (s u : ℕ) : ℚ := ((u - 1 : ℕ) : ℚ) / (s : ℚ)
def alpha (s u t : ℕ) : ℚ := 1 - gamma s u ^ t

lemma gamma_nonneg (s u : ℕ) : 0 ≤ gamma s u :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma gamma_lt_one {s u : ℕ} (hs : 0 < s) (hu : 1 ≤ u) (hus : u ≤ s) :
    gamma s u < 1 := by
  apply (div_lt_iff₀ (Nat.cast_pos.mpr hs)).mpr
  rw [one_mul]
  apply Nat.cast_lt.mpr
  exact (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hu) Nat.zero_lt_one).trans_le hus

theorem alpha_bounds {s u : ℕ} (hs : 0 < s) (hu : 1 ≤ u) (hus : u ≤ s) (t : ℕ) :
    0 ≤ alpha s u t ∧ alpha s u t ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (pow_le_one₀ (gamma_nonneg s u) (gamma_lt_one hs hu hus).le)
  · exact sub_le_self _ (pow_nonneg (gamma_nonneg s u) t)

@[simp] theorem alpha_zero (s u : ℕ) : alpha s u 0 = 0 := by simp [alpha]

theorem alpha_one_pos {s u : ℕ} (hs : 0 < s) (hu : 1 ≤ u) (hus : u ≤ s) :
    0 < alpha s u 1 := by simpa [alpha] using sub_pos.mpr (gamma_lt_one hs hu hus)

theorem alpha_monotone {s u : ℕ} (hs : 0 < s) (hu : 1 ≤ u) (hus : u ≤ s) :
    Monotone (alpha s u) := by
  intro a b hab
  exact sub_le_sub_left
    (pow_le_pow_of_le_one (gamma_nonneg s u) (gamma_lt_one hs hu hus).le hab) 1

/-- Initial preparation is counted separately from per-invocation preparation
and checking, but retained in the cumulative work counter. -/
structure CostState where
  invocations : ℕ
  preparation : ℕ
  checking : ℕ
  deriving DecidableEq

def initial (B : ℕ) : CostState := ⟨0, B, 0⟩
def invoke (W d t : ℕ) (st : CostState) : CostState :=
  ⟨st.invocations + 1, st.preparation + W, st.checking + d * t⟩

/-- Every invocation, including `t=0`, pays its scheduled preparation charge. -/
inductive Reachable (B W d : ℕ) : List ℕ → CostState → Prop where
  | init : Reachable B W d [] (initial B)
  | step {ts st} (h : Reachable B W d ts st) (t : ℕ) :
      Reachable B W d (ts ++ [t]) (invoke W d t st)

/-- All reachable prefixes satisfy the exact accounting invariant. -/
theorem reachable_invariant {B W d : ℕ} {ts : List ℕ} {st : CostState}
    (h : Reachable B W d ts st) :
    st.invocations = ts.length ∧
    st.preparation = B + st.invocations * W ∧
    st.checking = d * ts.sum := by
  induction h with
  | init => simp [initial]
  | @step ts st h t ih =>
      rcases ih with ⟨hc, hp, hk⟩
      simp only [invoke, List.length_append, List.length_singleton, List.sum_append,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      refine ⟨by simpa [hc], ?_, ?_⟩
      · rw [hp, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      · rw [hk, Nat.mul_add]

theorem reachable_total_cost {B W d : ℕ} {ts : List ℕ} {st : CostState}
    (h : Reachable B W d ts st) :
    st.preparation + st.checking = B + ts.length * W + d * ts.sum := by
  obtain ⟨hc, hp, hk⟩ := reachable_invariant h
  rw [hp, hk, hc]

/-- At a scheduled boundary, exactly a further `B` preparation operations
have been paid.  This is a work-credit theorem, not a matrix-correctness claim. -/
theorem next_buffer_work_by_R {B R W d : ℕ} {ts : List ℕ} {st : CostState}
    (h : Reachable B W d ts st) (hR : st.invocations = R) (hB : B = R * W) :
    st.preparation = B + B := by
  rw [(reachable_invariant h).2.1, hR, ← hB]

/-- Execute an arbitrary phase from its actual starting counters. -/
def runSchedule (W d : ℕ) : List ℕ → CostState → CostState
  | [], st => st
  | t :: ts, st => runSchedule W d ts (invoke W d t st)

/-- Every segment has exact counter increments, irrespective of interruption
patterns and independently of the starting phase number. -/
theorem runSchedule_increments (W d : ℕ) (ts : List ℕ) (st : CostState) :
    (runSchedule W d ts st).invocations = st.invocations + ts.length ∧
    (runSchedule W d ts st).preparation = st.preparation + ts.length * W ∧
    (runSchedule W d ts st).checking = st.checking + d * ts.sum := by
  induction ts generalizing st with
  | nil => simp [runSchedule]
  | cons t ts ih =>
      obtain ⟨hc, hp, hk⟩ := ih (invoke W d t st)
      simp only [runSchedule]
      refine ⟨?_, ?_, ?_⟩
      · rw [hc]
        simp only [invoke, List.length_cons]
        ring
      · rw [hp]
        simp only [invoke, List.length_cons]
        ring
      · rw [hk]
        simp only [invoke, List.sum_cons]
        ring

/-- Each complete R-invocation phase pays exactly B new work, including
phases containing zero-threshold invocations.  Assigning this work to a valid
next-buffer computation is a separate concrete-compiler obligation. -/
theorem every_phase_work_by_R (B R W d : ℕ) (ts : List ℕ) (st : CostState)
    (hR : ts.length = R) (hB : B = R * W) :
    (runSchedule W d ts st).preparation = st.preparation + B := by
  rw [(runSchedule_increments W d ts st).2.1, hR, ← hB]

theorem zero_threshold_charges_preparation (W d : ℕ) (st : CostState) :
    (invoke W d 0 st).preparation = st.preparation + W ∧
    (invoke W d 0 st).checking = st.checking := by simp [invoke]

theorem preparation_parameters : (4053532672 : ℕ) = 262144 * 15463 := by norm_num

/-- Exact-average form: after dividing by `N*d*1000000`, the actual
mean interruption depth `S/N` has overhead at most 0.491857 row equivalents.
This integer cross-product requires no rounding of the average depth. -/
theorem numeric_average_exact_cross_product (N S : ℕ) (hN : 262144 ≤ N) :
    1000000 * (4053532672 + N * 15463 + 62876 * S) ≤
      1000000 * 62876 * S + 491857 * N * 62876 := by
  have hB : 4053532672 ≤ N * 15463 := by
    calc
      4053532672 = 262144 * 15463 := preparation_parameters
      _ ≤ _ := Nat.mul_le_mul_right _ hN
  nlinarith

/-- Initialization-inclusive average bound, expressed without rounding or
natural-number division.  `S` is the sum of interruption depths, bounded by
`N*t`; multiplying by one million certifies the displayed decimal 0.491857. -/
theorem numeric_average_cross_product (N S t : ℕ)
    (hN : 262144 ≤ N) (hS : S ≤ N * t) :
    1000000 * (4053532672 + N * 15463 + 62876 * S) ≤
      N * 62876 * (1000000 * t + 491857) := by
  have hB : 4053532672 ≤ N * 15463 := by
    calc
      4053532672 = 262144 * 15463 := preparation_parameters
      _ ≤ _ := Nat.mul_le_mul_right _ hN
  have hcheck := Nat.mul_le_mul_left 62876 hS
  nlinarith

/-- For any invocation count beyond the first preparation period, every
average depth at most six costs strictly less than seven fresh checking rows,
including initialization and unused scheduled prefetch work. -/
theorem numeric_below_seven_rows (N S t : ℕ)
    (hN : 262144 ≤ N) (hS : S ≤ N * t) (ht : t ≤ 6) :
    4053532672 + N * 15463 + 62876 * S < N * 7 * 62876 := by
  have hB : 4053532672 ≤ N * 15463 := by
    calc
      4053532672 = 262144 * 15463 := preparation_parameters
      _ ≤ _ := Nat.mul_le_mul_right _ hN
  have hS6 : S ≤ N * 6 := hS.trans (Nat.mul_le_mul_left N ht)
  have hcheck := Nat.mul_le_mul_left 62876 hS6
  nlinarith

/-- Reachable-state specialization for arbitrary invocation depths, including
aborts.  The hypothesis is a pointwise depth cap, not a constant-depth run. -/
theorem reachable_below_seven_rows {ts : List ℕ} {st : CostState}
    (h : Reachable 4053532672 15463 62876 ts st)
    (hN : 262144 ≤ ts.length) (ht : ∀ t ∈ ts, t ≤ 6) :
    st.preparation + st.checking < ts.length * 7 * 62876 := by
  rw [reachable_total_cost h]
  apply numeric_below_seven_rows ts.length ts.sum 6 hN _ (le_refl _)
  simpa [nsmul_eq_mul] using List.sum_le_card_nsmul ts 6 ht

#print axioms alpha_bounds
#print axioms alpha_one_pos
#print axioms alpha_monotone
#print axioms reachable_total_cost
#print axioms next_buffer_work_by_R
#print axioms every_phase_work_by_R
#print axioms numeric_average_exact_cross_product
#print axioms numeric_average_cross_product
#print axioms reachable_below_seven_rows
end ProgressivePool.CostAndConfidence
