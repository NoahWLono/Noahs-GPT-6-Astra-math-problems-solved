import CodeBasisProperties
import WeightThirtyGraph
import QuadraticFourAudit
import WeightThirtyRankOneRows

namespace BooleanANF
open scoped BigOperators
open QuadraticFour

/-- In a one-dimensional actual coefficient code the unique basis word detects all
quadratic rows. -/
theorem rank_one_coefficient_rows {q : DoubleBlock → F₂}
    (e : (Fin 1 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (y : Block) :
    y ∈ coefficientRows q ↔ codeBasisWord e 0 y = 1 := by
  rw [codeBasisWord_detects_rows e]
  simp only [Fin.exists_fin_one]
  generalize codeBasisWord e 0 y = b
  fin_cases b <;> simp

/-- The number of actual quadratic rows in case d=1 is four or six. -/
theorem rank_one_coefficient_card {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 1 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) :
    (coefficientRows q).card = 4 ∨ (coefficientRows q).card = 6 := by
  have he : weight (codeBasisWord e 0) = (coefficientRows q).card := by
    rw [weight_eq_support_card]
    congr 1
    ext y
    simp [rank_one_coefficient_rows e]
  have hb : weight (codeBasisWord e 0) ≤ 7 := by
    rw [he]
    exact (Finset.card_le_card (coefficientRows_subset_active q)).trans h.activeBound
  rw [← he]
  exact quadratic_small_weight (codeBasisWord_degree h.totalDegree e 0)
    (codeBasisWord_ne_zero e 0) hb

/-- All quadratic rows have the very same actual polar, derived from the code
basis decomposition rather than supplied as a row-profile assumption. -/
theorem rank_one_row_polar {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 1 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q)
    {y : Block} (hy : y ∈ coefficientRows q) (x z : Block) :
    polar (fiber q y) x z = polar (quadraticBasisPart e 0) x z := by
  rw [quadraticPart_polar q y (h.rowDegree y)]
  have he : quadraticPart q y = quadraticBasisPart e 0 := by
    funext x
    rw [quadraticPart_code_expansion e]
    simp [(rank_one_coefficient_rows e y).mp hy]
  rw [he]

/-- Rows outside the coefficient support really are affine. -/
theorem affine_row_outside_coefficient_rows {q : DoubleBlock → F₂}
    (hr : ∀ y, HasDegreeLE (fiber q y) 2) {y : Block}
    (hy : y ∉ coefficientRows q) : HasDegreeLE (fiber q y) 1 := by
  intro s hs
  by_cases hc : s.card = 2
  · by_contra hn
    exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨s,hc⟩,hn⟩⟩)
  · exact hr y s (by omega)

/-- Every coefficient-active row is genuinely nonaffine. -/
theorem nonaffine_row_in_coefficient_rows {q : DoubleBlock → F₂}
    {y : Block} (hy : y ∈ coefficientRows q) : ¬ HasDegreeLE (fiber q y) 1 := by
  obtain ⟨s,hs⟩ := (Finset.mem_filter.mp hy).2
  intro ha
  exact hs (ha s.val (by omega))

theorem quadratic_cost_nonnegative {r : Block → F₂} (hr : HasDegreeLE r 2) :
    0 ≤ cost r := by
  by_cases hz : r = 0
  · rw [hz]; simp [cost, weight]
  · exact le_trans (by norm_num) (quadratic_min_cost hr hz)

/-- The budget excludes rank four for the common nonzero polar. -/
theorem rank_one_radical_card {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 1 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) :
    (radicalPoints (quadraticBasisPart e 0)).card = 4 := by
  have hn : ¬ HasDegreeLE (quadraticBasisPart e 0) 1 := by
    intro ha
    have hp := quadraticBasis_combination_polar_nonzero e
      (u := fun _ => 1) (by intro hz; have hh := congrFun hz 0; simp at hh)
    apply hp
    simpa using zero_polar_of_affine ha
  rcases nonaffine_radical_cards (quadraticBasisPart_degree e 0) hn with hh | hh
  · have hr (y : Block) (hy : y ∈ coefficientRows q) :
        (radicalPoints (fiber q y)).card = 1 := by
      have he : radicalPoints (fiber q y) = radicalPoints (quadraticBasisPart e 0) := by
        ext x
        simp only [radicalPoints, Finset.mem_filter, Finset.mem_univ, true_and,
          IsRadical, rank_one_row_polar h e hy]
      rw [he, hh]
    have hl (y : Block) : (if y ∈ coefficientRows q then 4 else 0 : ℤ) ≤
        cost (fiber q y) := by
      split_ifs with hy
      · exact radical_one_min_cost (h.rowDegree y) (hr y hy)
      · exact quadratic_cost_nonnegative (h.rowDegree y)
    have hs := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset Block)) => hl y)
    rw [h.costFourteen] at hs
    have he : (∑ y : Block, (if y ∈ coefficientRows q then 4 else 0 : ℤ)) =
        4 * ((coefficientRows q).card : ℤ) := by
      simp [Finset.sum_ite, nsmul_eq_mul, mul_comm]
    rw [he] at hs
    have hc := rank_one_coefficient_card h e
    omega
  · exact hh

 theorem rank_one_row_radical_card {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 1 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q)
    {y : Block} (hy : y ∈ coefficientRows q) : (radicalPoints (fiber q y)).card = 4 := by
  have he : radicalPoints (fiber q y) = radicalPoints (quadraticBasisPart e 0) := by
    ext x
    simp only [radicalPoints, Finset.mem_filter, Finset.mem_univ, true_and,
      IsRadical, rank_one_row_polar h e hy]
  rw [he, rank_one_radical_card h e]

/-- An affine-only extra row would spend the remaining six units and force
four identical cost-two rows. Their cancellation contradicts constant sum. -/
theorem rank_one_no_affine_extra {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 1 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) :
    activeRows q = coefficientRows q := by
  apply Finset.Subset.antisymm _ (coefficientRows_subset_active q)
  intro z hz
  by_contra hzs
  have hz0 : fiber q z ≠ 0 := (Finset.mem_filter.mp hz).2
  have hzc : 6 ≤ cost (fiber q z) :=
    affine_nonzero_min_cost (affine_row_outside_coefficient_rows h.rowDegree hzs) hz0
  let b : Block → ℤ := fun y => (if y = z then 6 else 0) +
    (if y ∈ coefficientRows q then 2 else 0)
  have hle (y : Block) : b y ≤ cost (fiber q y) := by
    by_cases hyz : y = z
    · subst y; simpa [b, hzs] using hzc
    · by_cases hys : y ∈ coefficientRows q
      · have hya := coefficientRows_subset_active q hys
        have hyn : fiber q y ≠ 0 := (Finset.mem_filter.mp hya).2
        simpa [b, hyz, hys] using quadratic_min_cost (h.rowDegree y) hyn
      · simpa [b, hyz, hys] using quadratic_cost_nonnegative (h.rowDegree y)
  have hbs : (∑ y, b y) = 6 + 2 * ((coefficientRows q).card : ℤ) := by
    simp [b, Finset.sum_add_distrib, Finset.sum_ite, nsmul_eq_mul, mul_comm]
  have hbound := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset Block)) => hle y)
  rw [h.costFourteen, hbs] at hbound
  have hc := rank_one_coefficient_card h e
  have hcard : (coefficientRows q).card = 4 := by omega
  have heq : ∀ y, b y = cost (fiber q y) := by
    intro y
    apply (Finset.sum_eq_sum_iff_of_le (fun y (_ : y ∈ (Finset.univ : Finset Block)) => hle y)).mp _ y (Finset.mem_univ y)
    rw [hbs, hcard, h.costFourteen]
    norm_num
  have hzc6 : cost (fiber q z) = 6 := by simpa [b, hzs] using (heq z).symm
  let p : Block → F₂ := radicalIndicator (quadraticBasisPart e 0)
  have hrow (y : Block) : fiber q y =
      (if y = z then fiber q z else if y ∈ coefficientRows q then p else 0) := by
    by_cases hyz : y = z
    · subst y; simp
    · by_cases hys : y ∈ coefficientRows q
      · have hc2 : cost (fiber q y) = 2 := by simpa [b, hyz, hys] using (heq y).symm
        simp only [hyz, hys, if_false, if_true]
        exact (cost_two_eq_radical (h.rowDegree y) hc2).trans
          (radicalIndicator_eq_of_polar_eq (rank_one_row_polar h e hys))
      · have hc0 : cost (fiber q y) = 0 := by simpa [b, hyz, hys] using (heq y).symm
        have hzrow : fiber q y = 0 := by
          by_cases hn : fiber q y = 0
          · exact hn
          · have hh := quadratic_min_cost (h.rowDegree y) hn
            omega
        simp [hyz, hys, hzrow]
  have hsum (x : Block) : (∑ y, fiber q y x) = fiber q z x := by
    calc
      (∑ y, fiber q y x) = ∑ y, (if y = z then fiber q z x else if y ∈ coefficientRows q then p x else 0) := by
        apply Finset.sum_congr rfl
        intro y hy
        simpa only [ite_apply, Pi.zero_apply] using congrFun (hrow y) x
      _ = fiber q z x := by
        have ht : (fun y => if y = z then fiber q z x else if y ∈ coefficientRows q then p x else 0) =
            fun y => (if y = z then fiber q z x else 0) + (if y ∈ coefficientRows q then p x else 0) := by
          funext y
          by_cases hy : y = z
          · subst y; simp [hzs]
          · simp [hy]
        rw [ht, Finset.sum_add_distrib]
        simp [Finset.sum_ite, hcard, nsmul_eq_mul]
        left; decide
  have hconstant : ∀ x, fiber q z x = fiber q z 0 := by
    intro x
    simpa [hsum] using h.sumConstant x
  have hbit : fiber q z 0 = 0 ∨ fiber q z 0 = 1 := by
    generalize fiber q z 0 = a
    fin_cases a <;> simp
  rcases hbit with hbit | hbit
  · have hh : fiber q z = 0 := by funext x; simpa [hbit] using hconstant x
    exact hz0 hh
  · have hh : fiber q z = fun _ => 1 := by funext x; simpa [hbit] using hconstant x
    rw [hh, cost_const_one] at hzc6
    omega

theorem rank_one_row_zero_outside {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 1 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q)
    {y : Block} (hy : y ∉ coefficientRows q) : fiber q y = 0 := by
  have hh : y ∉ activeRows q := by simpa [rank_one_no_affine_extra h e] using hy
  simpa [activeRows] using hh

theorem rank_one_cost_sum {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 1 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) :
    (∑ y ∈ coefficientRows q, cost (fiber q y)) = 14 := by
  rw [← h.costFourteen]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y hy hys
  rw [rank_one_row_zero_outside h e hys]
  simp [cost, weight]

/-- Six quadratic rows cannot have constant sum at total cost fourteen. -/
theorem rank_one_not_six {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 1 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q)
    (hcard : (coefficientRows q).card = 6) : False := by
  have hcost := rank_one_cost_sum h e
  obtain ⟨z,hzs,hz2⟩ : ∃ z ∈ coefficientRows q, cost (fiber q z) ≠ 2 := by
    by_contra hn
    have hh : ∀ z ∈ coefficientRows q, cost (fiber q z) = 2 := by simpa using hn
    simp only [Finset.sum_congr rfl hh, Finset.sum_const, hcard] at hcost
    norm_num at hcost
  have hzc : 4 ≤ cost (fiber q z) := by
    have hh := (rank_two_cost_data (h.rowDegree z) (rank_one_row_radical_card h e hzs)).1
    omega
  let b : Block → ℤ := fun y => 2 + if y = z then 2 else 0
  have hle (y : Block) (hy : y ∈ coefficientRows q) : b y ≤ cost (fiber q y) := by
    by_cases hyz : y = z
    · subst y; simpa [b] using hzc
    · have hyn : fiber q y ≠ 0 := (Finset.mem_filter.mp (coefficientRows_subset_active q hy)).2
      simpa [b, hyz] using quadratic_min_cost (h.rowDegree y) hyn
  have hbs : (∑ y ∈ coefficientRows q, b y) = 14 := by
    simp [b, Finset.sum_add_distrib, hcard, hzs]
  have heq (y : Block) (hy : y ∈ coefficientRows q) : b y = cost (fiber q y) :=
    (Finset.sum_eq_sum_iff_of_le hle).mp (hbs.trans hcost.symm) y hy
  have hzc4 : cost (fiber q z) = 4 := by simpa [b] using (heq z hzs).symm
  let p : Block → F₂ := radicalIndicator (quadraticBasisPart e 0)
  have hpc : cost p = 2 := radicalIndicator_cost (quadraticBasisPart_degree e 0)
    (rank_one_radical_card h e)
  have hrow (y : Block) (hy : y ∈ (coefficientRows q).erase z) : fiber q y = p := by
    have hyz := (Finset.mem_erase.mp hy).1
    have hys := (Finset.mem_erase.mp hy).2
    have hc2 : cost (fiber q y) = 2 := by simpa [b, hyz] using (heq y hys).symm
    exact (cost_two_eq_radical (h.rowDegree y) hc2).trans
      (radicalIndicator_eq_of_polar_eq (rank_one_row_polar h e hys))
  have hsum (x : Block) : (∑ y, fiber q y x) = fiber q z x + p x := by
    have hs : (∑ y, fiber q y x) = ∑ y ∈ coefficientRows q, fiber q y x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y hy hys
      rw [rank_one_row_zero_outside h e hys]
      rfl
    rw [hs, ← Finset.add_sum_erase _ _ hzs]
    have he : (∑ y ∈ (coefficientRows q).erase z, fiber q y x) =
        ∑ y ∈ (coefficientRows q).erase z, p x := by
      apply Finset.sum_congr rfl
      intro y hy
      exact congrFun (hrow y hy) x
    rw [he, Finset.sum_const, Finset.card_erase_of_mem hzs, hcard]
    norm_num only [Nat.reduceSub]
    have hf : 5 • p x = p x := by
      rw [nsmul_eq_mul]
      change (5 : F₂) * p x = p x
      have hh : (5 : F₂) = 1 := by decide
      rw [hh, one_mul]
    rw [hf]
  have hc : ∀ x, fiber q z x + p x = fiber q z 0 + p 0 := by
    intro x
    simpa [hsum] using h.sumConstant x
  have hh := constant_sum_costs (fiber q z) p hc
  omega

/-- The rank-one normalized residual has weight sixteen. -/
theorem rank_one_weight_sixteen {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 1 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) : weight q = 16 := by
  have hcard : (coefficientRows q).card = 4 := by
    rcases rank_one_coefficient_card h e with hc | hc
    · exact hc
    · exact (rank_one_not_six h e hc).elim
  let t : Fin 4 ≃ {y // y ∈ coefficientRows q} :=
    (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let r : Fin 4 → Block → F₂ := fun i => fiber q (t i).val
  have hreindex {A : Type} [AddCommMonoid A] (f : Block → A) :
      (∑ i : Fin 4, f (t i).val) = ∑ y ∈ coefficientRows q, f y := by
    exact (t.sum_comp (fun y => f y.val)).trans (Finset.sum_coe_sort _ f)
  have hcost : (∑ i, cost (r i)) = 14 := by
    change (∑ i, cost (fiber q (t i).val)) = 14
    rw [hreindex (fun y => cost (fiber q y))]
    exact rank_one_cost_sum h e
  have hcol (x : Block) : (∑ i, r i x) = ∑ y, fiber q y x := by
    change (∑ i, fiber q (t i).val x) = ∑ y, fiber q y x
    rw [hreindex (fun y => fiber q y x)]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y hy hys
    rw [rank_one_row_zero_outside h e hys]
    rfl
  have hw := rank_two_four_weight_sixteen r (fun i => h.rowDegree _)
    (fun i => rank_one_row_radical_card h e (t i).property)
    (fun i j x y => (rank_one_row_polar h e (t i).property x y).trans
      (rank_one_row_polar h e (t j).property x y).symm)
    hcost (by intro x; rw [hcol x, hcol 0]; exact h.sumConstant x)
  have hweights : (∑ i, weight (r i)) = weight q := by
    change (∑ i, weight (fiber q (t i).val)) = weight q
    rw [hreindex (fun y => weight (fiber q y)), ← weight_fibers q]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y hy hys
    rw [rank_one_row_zero_outside h e hys]
    simp [weight]
  omega

/-- Case d=1 for the actual coefficient code, with every row/profile link checked. -/
theorem weight_thirty_case_one {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 1) :
    TwoTransverseFlats (residualSignal q) := by
  exact weight_thirty_graph_of_weight_sixteen h
    (rank_one_weight_sixteen h (codeEquiv (quadraticCoefficientSpace q) 1 hd))

#print axioms weight_thirty_case_one
end BooleanANF
