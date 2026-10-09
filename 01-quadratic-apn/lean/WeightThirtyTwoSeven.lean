import WeightThirtyTwoPatterns
import QuadraticFourPairs
import QuadraticFourPolarRanks
import NormalizedCostBudget

namespace BooleanANF
open scoped BigOperators
open QuadraticFour

private theorem seven_row_nonaffine {q : DoubleBlock → F₂}
    {y : Block} (hy : y ∈ coefficientRows q) :
    ¬ HasDegreeLE (fiber q y) 1 := by
  obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hy).2
  intro ha
  exact hs (ha s.val (by omega))

private theorem seven_row_radical_card {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q) (hsize : (coefficientRows q).card = 7)
    {y : Block} (hy : y ∈ coefficientRows q) :
    (radicalPoints (fiber q y)).card = 4 := by
  rcases nonaffine_radical_cards (h.rowDegree y) (seven_row_nonaffine hy) with hr | hr
  · have hl := radical_one_min_cost (h.rowDegree y) hr
    have hc := normalized_seven_cost_two h hsize y hy
    omega
  · exact hr

private theorem pair_pattern_exists {a b : Block → F₂} {u v : F₂}
    (hc : 0 < pairPatternCount a b u v) : ∃ y, a y = u ∧ b y = v := by
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hc)
  refine ⟨y, ?_⟩
  by_contra hn
  simp [hn] at hy

private theorem rank_two_pattern_member {q : DoubleBlock → F₂}
    (e : (Fin 2 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q)
    {y : Block} {u v : F₂} (hy : codeBasisWord e 0 y = u ∧ codeBasisWord e 1 y = v)
    (hn : u ≠ 0 ∨ v ≠ 0) : y ∈ coefficientRows q := by
  rw [codeBasisWord_detects_rows e]
  rcases hn with hu | hv
  · exact ⟨0, by simpa [hy.1] using hu⟩
  · exact ⟨1, by simpa [hy.2] using hv⟩

/-- Each nonempty nonzero evaluation pattern has an actual rank-two polar
when the seven quadratic rows saturate the normalized cost budget. -/
theorem rank_two_seven_pattern_radical_card {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q) (hsize : (coefficientRows q).card = 7)
    (e : (Fin 2 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q)
    (u v : F₂) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : 0 < pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) u v) :
    (radicalPoints (fun x => u * quadraticBasisPart e 0 x +
      v * quadraticBasisPart e 1 x)).card = 4 := by
  obtain ⟨y, hy⟩ := pair_pattern_exists hc
  have hmem := rank_two_pattern_member e hy hn
  have he : radicalPoints (fiber q y) = radicalPoints
      (fun x => u * quadraticBasisPart e 0 x + v * quadraticBasisPart e 1 x) := by
    ext x
    simp only [radicalPoints, Finset.mem_filter, Finset.mem_univ, true_and, IsRadical,
      rank_two_row_polar h e y, hy.1, hy.2]
  rw [← he]
  exact seven_row_radical_card h hsize hmem

private theorem one_or_three_nsmul {n : ℕ} (hn : n = 1 ∨ n = 3) (z : F₂) :
    n • z = z := by
  rcases hn with rfl | rfl
  · simp
  · rw [nsmul_eq_mul]
    change (3 : F₂) * z = z
    have hthree : (3 : F₂) = 1 := by decide
    rw [hthree, one_mul]

/-- Seven actual quadratic rows cannot occur in a two-dimensional coefficient
code with odd multiplicities one or three for each of its nonzero patterns. -/
theorem rank_two_not_seven {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 2 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q)
    (hsize : (coefficientRows q).card = 7)
    (h10 : pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 1 0 = 1 ∨
      pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 1 0 = 3)
    (h01 : pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 0 1 = 1 ∨
      pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 0 1 = 3)
    (h11 : pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 1 1 = 1 ∨
      pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 1 1 = 3) : False := by
  let p := quadraticBasisPart e 0
  let r := quadraticBasisPart e 1
  have hp : (radicalPoints p).card = 4 := by
    simpa [p] using rank_two_seven_pattern_radical_card h hsize e 1 0
      (Or.inl one_ne_zero) (by omega)
  have hr : (radicalPoints r).card = 4 := by
    simpa [r] using rank_two_seven_pattern_radical_card h hsize e 0 1
      (Or.inr one_ne_zero) (by omega)
  have hpr : (radicalPoints (fun x => p x + r x)).card = 4 := by
    simpa [p, r] using rank_two_seven_pattern_radical_card h hsize e 1 1
      (Or.inl one_ne_zero) (by omega)
  let R : F₂ → F₂ → Block → F₂ := fun u v =>
    if u = 0 ∧ v = 0 then 0 else radicalIndicator (fun x => u * p x + v * r x)
  have hrow (y : Block) : fiber q y = R (codeBasisWord e 0 y) (codeBasisWord e 1 y) := by
    by_cases hz : codeBasisWord e 0 y = 0 ∧ codeBasisWord e 1 y = 0
    · have hyn : y ∉ coefficientRows q := by
        rw [codeBasisWord_detects_rows e]
        rintro ⟨i, hi⟩
        fin_cases i
        · exact hi hz.1
        · exact hi hz.2
      simp [R, hz, normalized_no_extra_affine h (by omega) y hyn]
    · have hmem : y ∈ coefficientRows q := rank_two_pattern_member e ⟨rfl, rfl⟩
        (not_and_or.mp hz)
      simp only [R, hz, if_false]
      exact (cost_two_eq_radical (h.rowDegree y) (normalized_seven_cost_two h hsize y hmem)).trans
        (radicalIndicator_eq_of_polar_eq (rank_two_row_polar h e y))
  have hsum (x : Block) : (∑ y : Block, fiber q y x) =
      radicalIndicator p x + radicalIndicator r x + radicalIndicator (fun z => p z + r z) x := by
    calc
      (∑ y : Block, fiber q y x) =
          ∑ y : Block, R (codeBasisWord e 0 y) (codeBasisWord e 1 y) x := by
        apply Finset.sum_congr rfl
        intro y _
        exact congrFun (hrow y) x
      _ = _ := by
        rw [pair_pattern_sum (codeBasisWord e 0) (codeBasisWord e 1) (fun u v => R u v x)]
        simp only [R, zero_mul, one_mul, add_zero, zero_add, and_self, if_true,
          one_ne_zero, false_and, and_false, if_false, Pi.zero_apply, smul_zero]
        rw [one_or_three_nsmul h10, one_or_three_nsmul h01, one_or_three_nsmul h11]
  apply pair_radical_sum_nonconstant (quadraticBasisPart_degree e 0)
    (quadraticBasisPart_degree e 1) hp hr hpr
  refine ⟨∑ y : Block, fiber q y 0, ?_⟩
  intro x
  rw [← hsum]
  exact h.sumConstant x

#print axioms rank_two_not_seven
end BooleanANF
