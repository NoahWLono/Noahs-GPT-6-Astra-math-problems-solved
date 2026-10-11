import Model

/-!
Independent semantic bridge from the executable mask to the paper's
square-difference predicate.  All finite boundary examples use kernel
reduction, without native evaluation.
-/

namespace Astra

theorem indicator_zero_or_one (m n a : ℕ) :
    indicator m n a = 0 ∨ indicator m n a = 1 := by
  by_cases hm : m = 0
  · subst m
    simp [indicator, mask]
  · have ha : a % m < m := Nat.mod_lt a (Nat.pos_of_ne_zero hm)
    simp [indicator, mask, List.getElem?_range ha]
    by_cases hc : ∃ b < m, a * a % m = (n + b * b) % m
    · exact Or.inr hc
    · exact Or.inl (by
        intro b hb he
        exact hc ⟨b, hb, he⟩)

theorem indicator_eq_ite_congruence (m n a : ℕ) (hm : 0 < m) :
    indicator m n a =
      if ∃ b < m, a * a % m = (n + b * b) % m then 1 else 0 := by
  by_cases hc : ∃ b < m, a * a % m = (n + b * b) % m
  · rw [if_pos hc]
    exact (indicator_eq_one_iff m n a hm).mpr hc
  · rw [if_neg hc]
    rcases indicator_zero_or_one m n a with hz | ho
    · exact hz
    · exact False.elim (hc ((indicator_eq_one_iff m n a hm).mp ho))

/-- The executable window is exactly the sum of the mathematical predicate. -/
theorem count_eq_sum_congruence (m n s h : ℕ) (hm : 0 < m) :
    count m n s h =
      ∑ j ∈ Finset.range h,
        if ∃ b < m, (s + j) * (s + j) % m = (n + b * b) % m
        then 1 else 0 := by
  induction h with
  | zero => simp [count, GenericWindow.window]
  | succ h ih =>
    rw [Finset.sum_range_succ]
    change count m n s h + indicator m n (s + h) = _
    rw [ih, indicator_eq_ite_congruence m n (s + h) hm]

/-- The minimax function is the supremum of the actual mathematical windows. -/
theorem F_eq_sup_congruence (m h : ℕ) (hm : 0 < m) :
    F m h =
      (Finset.range m).sup (fun n =>
        if Nat.gcd n m = 1 then
          (Finset.range m).sup (fun s =>
            ∑ j ∈ Finset.range h,
              if ∃ b < m, (s + j) * (s + j) % m = (n + b * b) % m
              then 1 else 0)
        else 0) := by
  unfold F
  congr 1
  funext n
  split_ifs
  · congr 1
    funext s
    exact count_eq_sum_congruence m n s h hm
  · rfl

theorem indicator_le_one (m n a : ℕ) : indicator m n a ≤ 1 := by
  rcases indicator_zero_or_one m n a with hz | ho <;> omega

theorem count_le_length (m n s h : ℕ) : count m n s h ≤ h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change count m n s h + indicator m n (s + h) ≤ h + 1
    have hi := indicator_le_one m n (s + h)
    omega

theorem F_le_length (m h : ℕ) : F m h ≤ h := by
  apply F_le_of_counts
  intro n _ s _
  exact count_le_length m n s h

theorem F_zero_length (m : ℕ) : F m 0 = 0 := by
  have hh := F_le_length m 0
  omega

/-- The paper's exceptional modulus-one unit convention is present. -/
example : IsUnit 1 0 := by decide

/-- Zero is a square: here the square difference is zero modulo nine. -/
example : indicator 9 1 1 = 1 := by decide

/-- Natural-number truncated subtraction would give the wrong answer here. -/
example : (0 - 1 : ℕ) % 4 = 0 ∧ indicator 4 1 0 = 0 := by decide

/-- Adjacent passing positions in the lower-density modulo-nine mask. -/
example : indicator 9 7 4 = 1 ∧ indicator 9 7 5 = 1 := by decide

/-- The short-window density-ranking reversal is present in the true maxima. -/
example : F 4 2 = 1 ∧ F 9 2 = 2 := by decide

/-- Longer windows repeat the modulus-one position rather than deduplicating. -/
example : count 1 0 0 7 = 7 ∧ F 1 7 = 7 := by decide

end Astra
