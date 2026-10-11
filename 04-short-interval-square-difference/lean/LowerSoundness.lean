import FiniteChecks

/-!
Logical extraction of the lower-bound facts from the executable checker.
This module performs no new native evaluation: it checks how the Boolean
certificate implies each proposition used in the all-length theorem.
-/

namespace Astra.Certificates

theorem lower_facts_of_checked (hchecked : lowerCheck = true) (m : ℕ)
    (hm1 : 1 ≤ m) (hm256 : m ≤ 256) (hne : m ≠ 144) :
    IsUnit m (lowerN m) ∧
      (∀ s < m, 2 * m ≤ 21 * count m (lowerN m) s m) ∧
      (∀ r < m, lowerS m r < m ∧
        2 * r ≤ 21 * count m (lowerN m) (lowerS m r) r) := by
  have hc := (List.all_eq_true.mp hchecked) m
    (List.mem_range.mpr (show m < 257 by omega))
  simp only [if_pos (And.intro hm1 hne)] at hc
  change
    ((decide (IsUnit m (lowerN m)) &&
        (List.range m).all (fun s =>
          decide (2 * m ≤ 21 * count m (lowerN m) s m))) &&
      (List.range m).all (fun r =>
        decide (lowerS m r < m ∧
          2 * r ≤ 21 * count m (lowerN m) (lowerS m r) r))) = true at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hc
  exact ⟨hc.1.1, hc.1.2, hc.2⟩

theorem lower_unit (m : ℕ)
    (hm1 : 1 ≤ m) (hm256 : m ≤ 256) (hne : m ≠ 144) :
    IsUnit m (lowerN m) :=
  (lower_facts_of_checked lower_checked m hm1 hm256 hne).1

theorem lower_period (m s : ℕ)
    (hm1 : 1 ≤ m) (hm256 : m ≤ 256) (hne : m ≠ 144) (hs : s < m) :
    2 * m ≤ 21 * count m (lowerN m) s m :=
  (lower_facts_of_checked lower_checked m hm1 hm256 hne).2.1 s hs

theorem lower_remainder (m r : ℕ)
    (hm1 : 1 ≤ m) (hm256 : m ≤ 256) (hne : m ≠ 144) (hr : r < m) :
    ∃ s, s < m ∧ 2 * r ≤ 21 * count m (lowerN m) s r := by
  exact ⟨lowerS m r, (lower_facts_of_checked lower_checked m hm1 hm256 hne).2.2 r hr⟩

end Astra.Certificates
