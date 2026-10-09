import WeightThirtyModel
import QuadraticFourAffine

namespace BooleanANF
open scoped BigOperators

theorem normalized_cost_nonnegative {r : Block → F₂} (hr : HasDegreeLE r 2) : 0 ≤ cost r := by
  by_cases hz : r = 0
  · simp [hz,cost,weight]
  · exact le_trans (by decide) (QuadraticFour.quadratic_min_cost hr hz)

theorem normalized_cost_even {r : Block → F₂} (hr : HasDegreeLE r 2) : cost r % 2 = 0 := by
  have hw := QuadraticFour.quadratic_even_weight hr
  unfold cost
  omega

theorem normalized_affine_outside {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    {y : Block} (hy : y ∉ coefficientRows q) : HasDegreeLE (fiber q y) 1 := by
  intro s hs
  by_cases hc : s.card = 2
  · by_contra hn
    exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨s,hc⟩,hn⟩⟩)
  · exact h.rowDegree y s (by omega)

theorem normalized_cost_ge_two {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    {y : Block} (hy : y ∈ coefficientRows q) : 2 ≤ cost (fiber q y) := by
  apply QuadraticFour.quadratic_min_cost (h.rowDegree y)
  exact (Finset.mem_filter.mp (coefficientRows_subset_active q hy)).2

private def extraBaseline (E : Finset Block) (y z : Block) : ℤ :=
  if z ∈ E then 2 else if z = y then 6 else 0

private theorem extra_baseline_le {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    {y : Block} (hy : y ∉ coefficientRows q) (hyn : fiber q y ≠ 0) (z : Block) :
    extraBaseline (coefficientRows q) y z ≤ cost (fiber q z) := by
  unfold extraBaseline
  split_ifs with hz hzy
  · exact normalized_cost_ge_two h hz
  · subst z
    exact QuadraticFour.affine_nonzero_min_cost (normalized_affine_outside h hy) hyn
  · exact normalized_cost_nonnegative (h.rowDegree z)

private theorem extra_baseline_sum (E : Finset Block) (y : Block) (hy : y ∉ E) :
    (∑ z : Block, extraBaseline E y z) = 2 * (E.card : ℤ) + 6 := by
  classical
  have he (z : Block) : extraBaseline E y z =
      (if z ∈ E then 2 else 0) + (if z = y then 6 else 0 : ℤ) := by
    by_cases hz : z ∈ E
    · have hzy : z ≠ y := fun he => hy (he ▸ hz)
      simp [extraBaseline,hz,hzy]
    · by_cases hzy : z = y <;> simp [extraBaseline,hz,hzy,hy]
  simp_rw [he]
  simp [Finset.sum_add_distrib, Finset.sum_ite, nsmul_eq_mul, mul_comm]

/-- Five or more quadratic rows leave no budget for an extra nonzero affine row. -/
theorem normalized_no_extra_affine {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hsize : 5 ≤ (coefficientRows q).card) :
    ∀ y, y ∉ coefficientRows q → fiber q y = 0 := by
  intro y hy
  by_contra hn
  have hs := Finset.sum_le_sum
    (fun z (_ : z ∈ (Finset.univ : Finset Block)) => extra_baseline_le h hy hn z)
  rw [extra_baseline_sum _ _ hy, h.costFourteen] at hs
  omega

/-- At four quadratic rows, an extra affine row saturates the entire cost budget. -/
theorem normalized_four_extra_boundary {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hsize : (coefficientRows q).card = 4) {y : Block}
    (hy : y ∉ coefficientRows q) (hyn : fiber q y ≠ 0) :
    cost (fiber q y) = 6 ∧
      (∀ z ∈ coefficientRows q, cost (fiber q z) = 2) ∧
      (∀ z, z ∉ insert y (coefficientRows q) → fiber q z = 0) := by
  have hnonneg (z : Block) := sub_nonneg.mpr (extra_baseline_le h hy hyn z)
  have hsum : (∑ z : Block, (cost (fiber q z) - extraBaseline (coefficientRows q) y z)) = 0 := by
    rw [Finset.sum_sub_distrib, h.costFourteen, extra_baseline_sum _ _ hy, hsize]
    norm_num
  have heq (z : Block) : cost (fiber q z) = extraBaseline (coefficientRows q) y z := by
    have hl := Finset.single_le_sum
      (fun w (_ : w ∈ (Finset.univ : Finset Block)) => hnonneg w) (Finset.mem_univ z)
    rw [hsum] at hl
    have hh := hnonneg z
    omega
  refine ⟨?_,?_,?_⟩
  · simpa [extraBaseline,hy] using heq y
  · intro z hz
    simpa [extraBaseline,hz] using heq z
  · intro z hz
    have hzE : z ∉ coefficientRows q := fun he => hz (Finset.mem_insert_of_mem he)
    have hzy : z ≠ y := fun he => hz (by simp [he])
    have hc : cost (fiber q z) = 0 := by simpa [extraBaseline,hzE,hzy] using heq z
    by_contra hn
    have hm := QuadraticFour.quadratic_min_cost (h.rowDegree z) hn
    omega

theorem normalized_coefficient_cost_sum {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hextra : ∀ y, y ∉ coefficientRows q → fiber q y = 0) :
    (∑ y ∈ coefficientRows q, cost (fiber q y)) = 14 := by
  rw [← h.costFourteen]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y hy hyn
  simp [hextra y hyn,cost,weight]

/-- Seven quadratic rows all attain the unique minimal cost two. -/
theorem normalized_seven_cost_two {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hsize : (coefficientRows q).card = 7) :
    ∀ y ∈ coefficientRows q, cost (fiber q y) = 2 := by
  have hx := normalized_no_extra_affine h (by omega)
  have hc := normalized_coefficient_cost_sum h hx
  have hsum : (∑ y ∈ coefficientRows q, (cost (fiber q y) - 2)) = 0 := by
    rw [Finset.sum_sub_distrib, hc]
    simp [hsize]
  intro y hy
  have hm := normalized_cost_ge_two h hy
  have ht := Finset.single_le_sum
    (fun z hz => sub_nonneg.mpr (normalized_cost_ge_two h hz)) hy
  rw [hsum] at ht
  omega

/-- Six quadratic rows have one cost-four row and five cost-two rows. -/
theorem normalized_six_costs {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hsize : (coefficientRows q).card = 6) :
    ∃ y ∈ coefficientRows q, cost (fiber q y) = 4 ∧
      ∀ z ∈ coefficientRows q, z ≠ y → cost (fiber q z) = 2 := by
  have hx := normalized_no_extra_affine h (by omega)
  have hc := normalized_coefficient_cost_sum h hx
  have hsum : (∑ y ∈ coefficientRows q, (cost (fiber q y) - 2)) = 2 := by
    rw [Finset.sum_sub_distrib, hc]
    simp [hsize]
  obtain ⟨y,hy,hyn⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show
      (∑ y ∈ coefficientRows q, (cost (fiber q y) - 2)) ≠ 0 by rw [hsum]; decide)
  have hm := normalized_cost_ge_two h hy
  have hev := normalized_cost_even (h.rowDegree y)
  have ht := Finset.single_le_sum
    (fun z hz => sub_nonneg.mpr (normalized_cost_ge_two h hz)) hy
  rw [hsum] at ht
  have hcy : cost (fiber q y) = 4 := by omega
  refine ⟨y,hy,hcy,?_⟩
  have he := Finset.sum_erase_add (coefficientRows q) (fun z => cost (fiber q z)-2) hy
  dsimp only at he
  rw [hsum,hcy] at he
  have hrest : (∑ z ∈ (coefficientRows q).erase y, (cost (fiber q z)-2)) = 0 := by omega
  intro z hz hzy
  have hzm := normalized_cost_ge_two h hz
  have hzmem : z ∈ (coefficientRows q).erase y := Finset.mem_erase.mpr ⟨hzy,hz⟩
  have hzt := Finset.single_le_sum
    (fun w hw => sub_nonneg.mpr (normalized_cost_ge_two h (Finset.mem_of_mem_erase hw))) hzmem
  rw [hrest] at hzt
  omega

end BooleanANF
