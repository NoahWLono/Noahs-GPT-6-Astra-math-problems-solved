import QuadraticCoefficientCode
import BinaryPatternCounts

namespace BooleanANF
open scoped BigOperators

/-- Support containment controls actual Hamming weight. -/
theorem weight_le_card_of_supported {Y : Type*} [DecidableEq Y] [Fintype Y]
    (f : Y → F₂) (E : Finset Y) (hf : ∀ y, y ∉ E → f y = 0) : weight f ≤ E.card := by
  rw [weight_eq_support_card]
  apply Finset.card_le_card
  intro y hy
  by_contra hn
  have h1 := (Finset.mem_filter.mp hy).2
  have h0 := hf y hn
  rw [h0] at h1
  exact zero_ne_one h1

theorem pair_pattern_total {Y : Type*} [DecidableEq Y] [Fintype Y] (a b : Y → F₂) :
    pairPatternCount a b 1 0 + pairPatternCount a b 0 1 + pairPatternCount a b 1 1 =
      (Finset.univ.filter (fun y => a y ≠ 0 ∨ b y ≠ 0)).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [pairPatternCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  generalize a y = u
  generalize b y = v
  fin_cases u <;> fin_cases v <;> decide

/-- The actual d=2 coefficient evaluation patterns obey precisely the two numerical profiles. -/
theorem coefficient_pair_patterns {q : DoubleBlock → F₂}
    (hq : HasDegreeLE q 4) (hs : (activeRows q).card ≤ 7)
    (a b : Block → F₂) (ha : a ∈ quadraticCoefficientSpace q)
    (hb : b ∈ quadraticCoefficientSpace q)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab0 : a+b ≠ 0) :
    let n10 := pairPatternCount a b 1 0
    let n01 := pairPatternCount a b 0 1
    let n11 := pairPatternCount a b 1 1
    (n10=2 ∧ n01=2 ∧ n11=2) ∨ (n10=1 ∧ n01=3 ∧ n11=3) ∨
    (n10=3 ∧ n01=1 ∧ n11=3) ∨ (n10=3 ∧ n01=3 ∧ n11=1) := by
  have hw (g : Block → F₂) (hg : g ∈ quadraticCoefficientSpace q) (hg0 : g ≠ 0) :
      weight g = 4 ∨ weight g = 6 := by
    apply QuadraticFour.quadratic_small_weight (quadraticCoefficientSpace_degree hq hg) hg0
    exact (weight_le_card_of_supported g (activeRows q)
      (quadraticCoefficientSpace_supported q hg)).trans hs
  have hwa := hw a ha ha0
  change weight (fun y => a y) = 4 ∨ weight (fun y => a y) = 6 at hwa
  have hwb := hw b hb hb0
  change weight (fun y => b y) = 4 ∨ weight (fun y => b y) = 6 at hwb
  have hwab := hw (a+b) ((quadraticCoefficientSpace q).add_mem ha hb) hab0
  have h1 := pair_pattern_weight a b 1 0
  have h2 := pair_pattern_weight a b 0 1
  have h3 := pair_pattern_weight a b 1 1
  simp only [zero_mul, one_mul, zero_add, add_zero, CharTwo.add_self_eq_zero,
    show (0 : F₂).val = 0 from rfl, show (1 : F₂).val = 1 from rfl] at h1 h2 h3
  have hsize : pairPatternCount a b 1 0 + pairPatternCount a b 0 1 +
      pairPatternCount a b 1 1 ≤ 7 := by
    rw [pair_pattern_total]
    apply le_trans (Finset.card_le_card ?_) hs
    intro y hy
    by_contra hn
    have hza := quadraticCoefficientSpace_supported q ha y hn
    have hzb := quadraticCoefficientSpace_supported q hb y hn
    rcases (Finset.mem_filter.mp hy).2 with h | h
    · exact h hza
    · exact h hzb
  apply two_dimensional_pattern_counts _ _ _ hsize
  · omega
  · omega
  · change weight (fun y => a y+b y) = 4 ∨ weight (fun y => a y+b y) = 6 at hwab
    omega

end BooleanANF
