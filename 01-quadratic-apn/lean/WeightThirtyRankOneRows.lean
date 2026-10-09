import QuadraticFourAudit
set_option maxHeartbeats 2000000

namespace BooleanANF
open scoped BigOperators
open QuadraticFour

/-- Cost parity and low-cost weight for a rank-two row. -/
theorem rank_two_cost_data {r : Block → F₂} (hr : HasDegreeLE r 2)
    (hk : (radicalPoints r).card = 4) :
    (cost r = 2 ∨ cost r = 4 ∨ cost r = 6 ∨ cost r = 8 ∨ cost r = 10 ∨ cost r = 12) ∧
    (cost r ≤ 4 → weight r = 4) := by
  have hw := radical_four_weights hr hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  have hb := ZMod.val_lt (r 0)
  unfold cost
  omega

/-- If two cost-two rows cancel, their two remaining companions would have
constant sum. Their costs sum to ten, which excludes both equality and complement. -/
theorem rank_two_four_no_two_cost_two
    (a b c d : Block → F₂)
    (ha : HasDegreeLE a 2) (hb : HasDegreeLE b 2)
    (hp : ∀ x y, polar a x y = polar b x y)
    (ha2 : cost a = 2) (hb2 : cost b = 2)
    (hc : cost c = 2 ∨ cost c = 4 ∨ cost c = 6 ∨ cost c = 8 ∨ cost c = 10 ∨ cost c = 12)
    (hd : cost d = 2 ∨ cost d = 4 ∨ cost d = 6 ∨ cost d = 8 ∨ cost d = 10 ∨ cost d = 12)
    (hbudget : cost a + cost b + cost c + cost d = 14)
    (hsum : ∀ x, a x + b x + c x + d x = a 0 + b 0 + c 0 + d 0) : False := by
  have he := cost_two_unique ha hb hp ha2 hb2
  subst b
  have hh : ∀ x, c x + d x = c 0 + d 0 := by
    intro x
    simpa only [CharTwo.add_self_eq_zero, zero_add] using hsum x
  have hcc := constant_sum_costs c d hh
  omega

/-- The entire four-row d=1 cost partition exclusion, using only actual quadratic
facts and constant sum. No balanced-affine-image lemma is needed. -/
theorem rank_two_four_weight_sixteen (r : Fin 4 → Block → F₂)
    (hr : ∀ i, HasDegreeLE (r i) 2)
    (hk : ∀ i, (radicalPoints (r i)).card = 4)
    (hp : ∀ i j x y, polar (r i) x y = polar (r j) x y)
    (hbudget : (∑ i, cost (r i)) = 14)
    (hsum : ∀ x, (∑ i, r i x) = ∑ i, r i 0) :
    (∑ i, weight (r i)) = 16 := by
  have hd := fun i => rank_two_cost_data (hr i) (hk i)
  have hb : cost (r 0) + cost (r 1) + cost (r 2) + cost (r 3) = 14 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hbudget
  have hs : ∀ x, r 0 x + r 1 x + r 2 x + r 3 x =
      r 0 0 + r 1 0 + r 2 0 + r 3 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have h01 : ¬ (cost (r 0) = 2 ∧ cost (r 1) = 2) := by
    rintro ⟨h0,h1⟩
    exact rank_two_four_no_two_cost_two _ _ _ _ (hr 0) (hr 1) (hp 0 1)
      h0 h1 (hd 2).1 (hd 3).1 hb hs
  have h02 : ¬ (cost (r 0) = 2 ∧ cost (r 2) = 2) := by
    rintro ⟨h0,h2⟩
    apply rank_two_four_no_two_cost_two (r 0) (r 2) (r 1) (r 3)
      (hr 0) (hr 2) (hp 0 2) h0 h2 (hd 1).1 (hd 3).1
    · omega
    · intro x; convert hs x using 1 <;> ring
  have h03 : ¬ (cost (r 0) = 2 ∧ cost (r 3) = 2) := by
    rintro ⟨h0,h3⟩
    apply rank_two_four_no_two_cost_two (r 0) (r 3) (r 1) (r 2)
      (hr 0) (hr 3) (hp 0 3) h0 h3 (hd 1).1 (hd 2).1
    · omega
    · intro x; convert hs x using 1 <;> ring
  have h12 : ¬ (cost (r 1) = 2 ∧ cost (r 2) = 2) := by
    rintro ⟨h1,h2⟩
    apply rank_two_four_no_two_cost_two (r 1) (r 2) (r 0) (r 3)
      (hr 1) (hr 2) (hp 1 2) h1 h2 (hd 0).1 (hd 3).1
    · omega
    · intro x; convert hs x using 1 <;> ring
  have h13 : ¬ (cost (r 1) = 2 ∧ cost (r 3) = 2) := by
    rintro ⟨h1,h3⟩
    apply rank_two_four_no_two_cost_two (r 1) (r 3) (r 0) (r 2)
      (hr 1) (hr 3) (hp 1 3) h1 h3 (hd 0).1 (hd 2).1
    · omega
    · intro x; convert hs x using 1 <;> ring
  have h23 : ¬ (cost (r 2) = 2 ∧ cost (r 3) = 2) := by
    rintro ⟨h2,h3⟩
    apply rank_two_four_no_two_cost_two (r 2) (r 3) (r 0) (r 1)
      (hr 2) (hr 3) (hp 2 3) h2 h3 (hd 0).1 (hd 1).1
    · omega
    · intro x; convert hs x using 1 <;> ring
  have hl0 : cost (r 0) = 2 ∨ 4 ≤ cost (r 0) := by have hh := (hd 0).1; omega
  have hl1 : cost (r 1) = 2 ∨ 4 ≤ cost (r 1) := by have hh := (hd 1).1; omega
  have hl2 : cost (r 2) = 2 ∨ 4 ≤ cost (r 2) := by have hh := (hd 2).1; omega
  have hl3 : cost (r 3) = 2 ∨ 4 ≤ cost (r 3) := by have hh := (hd 3).1; omega
  have hw0 : weight (r 0) = 4 := (hd 0).2 (by omega)
  have hw1 : weight (r 1) = 4 := (hd 1).2 (by omega)
  have hw2 : weight (r 2) = 4 := (hd 2).2 (by omega)
  have hw3 : weight (r 3) = 4 := (hd 3).2 (by omega)
  simp [Fin.sum_univ_succ, hw0, hw1, hw2, hw3]

#print axioms rank_two_four_weight_sixteen
end BooleanANF
