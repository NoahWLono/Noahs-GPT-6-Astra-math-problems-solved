import WeightThirtyModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The incidence-moment argument for seven radical planes. The points are the
fifteen nonzero vectors of a four-dimensional binary space. -/
namespace SevenPlaneIncidence
open scoped BigOperators

/-- The two incidence moments force one common point and no other overlaps. -/
theorem unique_common_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 15) (r : ι → ℤ)
    (hlo : ∀ x, 1 ≤ r x) (hhi : ∀ x, r x ≤ 7)
    (hfirst : ∑ x, r x = 21)
    (hsecond : ∑ x, r x * (r x - 1) = 42) :
    ∃! p, r p = 7 := by
  classical
  have hdef : ∑ x, (r x - 1) * (7 - r x) = 0 := by
    have heq : (∑ x, (r x - 1) * (7 - r x)) =
        7 * (∑ x, r x) - (∑ x, r x * (r x - 1)) - 7 * Fintype.card ι := by
      calc
        _ = ∑ x, (7 * r x - r x * (r x - 1) - 7) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = _ := by simp [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, mul_comm]
    rw [heq, hfirst, hsecond, hcard]
    norm_num
  have hnonneg : ∀ x, 0 ≤ (r x - 1) * (7 - r x) := fun x =>
    mul_nonneg (sub_nonneg.mpr (hlo x)) (sub_nonneg.mpr (hhi x))
  have hend : ∀ x, r x = 1 ∨ r x = 7 := by
    intro x
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hnonneg x)).mp hdef x (Finset.mem_univ x)
    rcases mul_eq_zero.mp hz with h | h
    · left; omega
    · right; omega
  have hex : ∃ p, r p = 7 := by
    apply Classical.byContradiction
    intro hn
    have hall : ∀ x, r x = 1 := fun x => (hend x).resolve_right (fun h => hn ⟨x,h⟩)
    simp only [hall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hfirst
    omega
  obtain ⟨p,hp⟩ := hex
  refine ⟨p,hp,?_⟩
  intro y hy
  by_cases hne : y = p
  · exact hne
  · have hs : ∑ x, (r x - 1) = 6 := by
      simp only [Finset.sum_sub_distrib, hfirst, Finset.sum_const, Finset.card_univ,
        hcard, nsmul_eq_mul]
      norm_num
    have hle : ∑ x ∈ ({p,y} : Finset ι), (r x - 1) ≤ ∑ x, (r x - 1) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ => sub_nonneg.mpr (hlo x))
    rw [Finset.sum_pair (Ne.symm hne), hp, hy, hs] at hle
    norm_num at hle

/-- Double counting derives both moments directly from the seven plane rows:
three nonzero points on each plane and one on every distinct pair. -/
theorem incidence_moments {I X : Type*} [Fintype I] [Fintype X]
    (hseven : Fintype.card I = 7) (b : I → X → ℤ)
    (hbit : ∀ i x, b i x = 0 ∨ b i x = 1)
    (hrow : ∀ i, ∑ x, b i x = 3)
    (hpair : ∀ i j, i ≠ j → ∑ x, b i x * b j x = 1) :
    (∑ x, ∑ i, b i x) = 21 ∧
    (∑ x, (∑ i, b i x) * ((∑ i, b i x) - 1)) = 42 := by
  classical
  have hfirst : (∑ x, ∑ i, b i x) = 21 := by
    rw [Finset.sum_comm]
    simp [hrow, hseven]
  have hdot : ∀ i j, (∑ x, b i x * b j x) = 1 + if i=j then 2 else 0 := by
    intro i j
    by_cases h : i=j
    · subst j
      rw [if_pos rfl]
      have he : ∀ x, b i x * b i x = b i x := by
        intro x
        rcases hbit i x with h | h <;> simp [h]
      simp only [he, hrow]
      norm_num
    · rw [if_neg h, add_zero]
      exact hpair i j h
  have hsquare : (∑ x, (∑ i, b i x) * (∑ i, b i x)) = 63 := by
    calc
      _ = ∑ x, ∑ i, ∑ j, b i x * b j x := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, ∑ x, b i x * b j x := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = 63 := by simp [hdot, Finset.sum_add_distrib, hseven]
  refine ⟨hfirst, ?_⟩
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsquare, hfirst]
  norm_num

/-- Seven three-point rows on fifteen points, pairwise meeting once, have a
unique common point as soon as their union covers all fifteen points. -/
theorem seven_rows_common_point {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    (hseven : Fintype.card I = 7) (hcard : Fintype.card X = 15) (b : I → X → ℤ)
    (hbit : ∀ i x, b i x = 0 ∨ b i x = 1)
    (hrow : ∀ i, ∑ x, b i x = 3)
    (hpair : ∀ i j, i ≠ j → ∑ x, b i x * b j x = 1)
    (hcover : ∀ x, ∃ i, b i x = 1) :
    ∃! p, ∀ i, b i p = 1 := by
  classical
  have hnonneg : ∀ i x, 0 ≤ b i x := by
    intro i x
    rcases hbit i x with h | h <;> omega
  have hone : ∀ i x, b i x ≤ 1 := by
    intro i x
    rcases hbit i x with h | h <;> omega
  have hlo : ∀ x, 1 ≤ ∑ i, b i x := by
    intro x
    obtain ⟨i,hi⟩ := hcover x
    rw [← hi]
    exact Finset.single_le_sum (fun j _ => hnonneg j x) (Finset.mem_univ i)
  have hhi : ∀ x, (∑ i, b i x) ≤ 7 := by
    intro x
    calc
      _ ≤ ∑ _i : I, (1 : ℤ) := Finset.sum_le_sum (fun i _ => hone i x)
      _ = 7 := by simp [hseven]
  have heq : ∀ x, (∑ i, b i x) = 7 ↔ ∀ i, b i x = 1 := by
    intro x
    constructor
    · intro hx i
      have hs : (∑ j, (1-b j x)) = 0 := by simp [Finset.sum_sub_distrib, hx, hseven]
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sub_nonneg.mpr (hone j x))).mp hs i (Finset.mem_univ i)
      omega
    · intro hx
      simp [hx, hseven]
  obtain ⟨hfirst,hsecond⟩ := incidence_moments hseven b hbit hrow hpair
  obtain ⟨p,hp,hunique⟩ := unique_common_point hcard (fun x => ∑ i, b i x)
    hlo hhi hfirst hsecond
  refine ⟨p,(heq p).mp hp,?_⟩
  intro y hy
  exact hunique y ((heq y).mpr hy)

end SevenPlaneIncidence
