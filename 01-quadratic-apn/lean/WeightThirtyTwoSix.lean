import WeightThirtyTwoPatterns
import QuadraticFourRadical
import QuadraticFourCostComplement

namespace BooleanANF
open scoped BigOperators
open QuadraticFour
set_option maxHeartbeats 400000

private theorem pattern_two_self (a b : Block → F₂)
    (h10 : pairPatternCount a b 1 0 = 2)
    (h01 : pairPatternCount a b 0 1 = 2)
    (h11 : pairPatternCount a b 1 1 = 2)
    (u v : F₂) (hn : u ≠ 0 ∨ v ≠ 0) : pairPatternCount a b u v = 2 := by
  fin_cases u <;> fin_cases v
  · simp at hn
  · exact h01
  · exact h10
  · exact h11

theorem rank_two_six_exclusion {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 2 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q)
    (h10 : pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 1 0 = 2)
    (h01 : pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 0 1 = 2)
    (h11 : pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 1 1 = 2) : False := by
  let a := codeBasisWord e 0
  let b := codeBasisWord e 1
  have hcard : (coefficientRows q).card = 6 := by
    have ht := rank_two_pattern_total e
    omega
  obtain ⟨z,hz,hzc,hrest⟩ := normalized_six_costs h hcard
  let E := Finset.univ.filter (fun y => a y = a z ∧ b y = b z)
  have hE : E.card = 2 := by
    have hn := (rank_two_coefficient_rows e z).mp hz
    have he : E.card = pairPatternCount a b (a z) (b z) := by
      change (Finset.univ.filter (fun y => a y = a z ∧ b y = b z)).card = _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rfl
    rw [he]
    change pairPatternCount a b 1 0 = 2 at h10
    change pairPatternCount a b 0 1 = 2 at h01
    change pairPatternCount a b 1 1 = 2 at h11
    change a z ≠ 0 ∨ b z ≠ 0 at hn
    exact pattern_two_self a b h10 h01 h11 (a z) (b z) hn
  obtain ⟨w,hw,hwz⟩ := Finset.exists_mem_ne (show 1 < E.card by omega) z
  have hwab := (Finset.mem_filter.mp hw).2
  have hwc : w ∈ coefficientRows q := by
    rw [rank_two_coefficient_rows e]
    change a w ≠ 0 ∨ b w ≠ 0
    rw [hwab.1,hwab.2]
    exact (rank_two_coefficient_rows e z).mp hz
  have hwcost := hrest w hwc hwz
  let R : F₂ → F₂ → Block → F₂ := fun u v =>
    if u = 0 ∧ v = 0 then 0 else radicalIndicator
      (fun x => u * quadraticBasisPart e 0 x + v * quadraticBasisPart e 1 x)
  have hrow (y : Block) (hyz : y ≠ z) : fiber q y = R (a y) (b y) := by
    by_cases hy : y ∈ coefficientRows q
    · have hn : ¬(a y = 0 ∧ b y = 0) := by
        have hh := (rank_two_coefficient_rows e y).mp hy
        change a y ≠ 0 ∨ b y ≠ 0 at hh
        exact fun hh0 => hh.elim (fun hn => hn hh0.1) (fun hn => hn hh0.2)
      simp only [R,if_neg hn]
      exact (cost_two_eq_radical (h.rowDegree y) (hrest y hy hyz)).trans
        (radicalIndicator_eq_of_polar_eq (rank_two_row_polar h e y))
    · have hn : a y = 0 ∧ b y = 0 := by
        have hh := (rank_two_coefficient_rows e y).not.mp hy
        push_neg at hh
        exact hh
      rw [normalized_no_extra_affine h (by omega) y hy]
      simp [R,hn]
  have hRcost : cost (R (a z) (b z)) = 2 := by
    have he := hrow w hwz
    rw [hwab.1,hwab.2] at he
    rw [← he]
    exact hwcost
  have hRsum (x : Block) : (∑ y, R (a y) (b y) x) = 0 := by
    rw [pair_pattern_sum a b (fun u v => R u v x)]
    change pairPatternCount a b 1 0 = 2 at h10
    change pairPatternCount a b 0 1 = 2 at h01
    change pairPatternCount a b 1 1 = 2 at h11
    rw [h10,h01,h11]
    have ht : (2 : F₂) = 0 := by decide
    simp [R,nsmul_eq_mul,ht]
  have hsum (x : Block) : (∑ y, fiber q y x) = fiber q z x + R (a z) (b z) x := by
    have he (y : Block) : fiber q y x = R (a y) (b y) x +
        if y = z then fiber q z x + R (a z) (b z) x else 0 := by
      by_cases hy : y = z
      · subst y
        simp [add_assoc,add_left_comm,CharTwo.add_self_eq_zero]
      · simp [hy,hrow y hy]
    calc
      (∑ y, fiber q y x) = ∑ y, (R (a y) (b y) x +
          if y = z then fiber q z x + R (a z) (b z) x else 0) :=
        Finset.sum_congr rfl (fun y _ => he y)
      _ = _ := by rw [Finset.sum_add_distrib,hRsum]; simp
  have hc : ∀ x, fiber q z x + R (a z) (b z) x =
      fiber q z 0 + R (a z) (b z) 0 := by
    intro x
    simpa [hsum] using h.sumConstant x
  have hh := constant_sum_costs (fiber q z) (R (a z) (b z)) hc
  omega
end BooleanANF
