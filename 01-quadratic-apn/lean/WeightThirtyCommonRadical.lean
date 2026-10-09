import SevenPlaneIncidence
import QuadraticFourPairs
import QuadraticFourCosets
import NormalizedCostBudget
import SimplexLabels

/-! The common radical of the seven minimal-cost rows. All radicals below are
those of the actual Boolean quadratic functions, not auxiliary rank data. -/
namespace BooleanANF
open scoped BigOperators
open QuadraticFour

private theorem zero_isRadical (r : Block → F₂) : IsRadical r 0 := by
  intro y
  simp [polar, CharTwo.add_self_eq_zero, add_assoc, add_comm, add_left_comm]

/-- The actual polar radical of a cost-two quadratic has four elements. -/
theorem cost_two_radical_card {r : Block → F₂} (hr : HasDegreeLE r 2)
    (hc : cost r = 2) : (radicalPoints r).card = 4 := by
  have he := cost_two_eq_radical hr hc
  have hzero : r 0 = 1 := by rw [he]; exact radicalIndicator_zero r
  have hw : weight r = (radicalPoints r).card := by
    conv_lhs => rw [he]
    exact weight_radicalIndicator r
  unfold cost at hc
  rw [hzero, hw] at hc
  change ((radicalPoints r).card : ℤ) - 2 * 1 = 2 at hc
  omega

private theorem sum_nonzero_add_zero {A : Type*} [AddCommMonoid A] (f : Block → A) :
    (∑ x : {x : Block // x ≠ 0}, f x) + f 0 = ∑ x : Block, f x := by
  rw [← Finset.sum_subtype (Finset.univ.erase 0) (by simp)]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ 0)

private theorem radical_integer_sum (r : Block → F₂) :
    (∑ x : Block, if IsRadical r x then (1 : ℤ) else 0) = (radicalPoints r).card := by
  simp [radicalPoints, Finset.sum_boole]

private theorem radical_pair_integer_sum (r s : Block → F₂) :
    (∑ x : Block, (if IsRadical r x then (1 : ℤ) else 0) *
      (if IsRadical s x then 1 else 0)) = (radicalPoints r ∩ radicalPoints s).card := by
  have he (x : Block) : (if IsRadical r x then (1 : ℤ) else 0) *
      (if IsRadical s x then 1 else 0) = if IsRadical r x ∧ IsRadical s x then 1 else 0 := by
    split_ifs <;> simp_all
  simp_rw [he]
  have hf : radicalPoints r ∩ radicalPoints s =
      Finset.univ.filter (fun x => IsRadical r x ∧ IsRadical s x) := by
    ext x
    simp [radicalPoints]
  rw [hf]
  simp [Finset.sum_boole]

/-- Seven actual cost-two quadratic rows with pairwise line intersections and
constant sum have a unique common nonzero polar-radical vector. -/
theorem seven_cost_two_common_radical {I : Type*} [Fintype I]
    (hseven : Fintype.card I = 7) (r : I → Block → F₂)
    (hdegree : ∀ i, HasDegreeLE (r i) 2) (hcost : ∀ i, cost (r i) = 2)
    (hpair : ∀ i j, i ≠ j → (radicalPoints (r i) ∩ radicalPoints (r j)).card = 2)
    (hconstant : ∀ x, (∑ i, r i x) = ∑ i, r i 0) :
    ∃! p : {x : Block // x ≠ 0}, ∀ i, IsRadical (r i) p := by
  classical
  let X := {x : Block // x ≠ 0}
  let b : I → X → ℤ := fun i x => if IsRadical (r i) x then 1 else 0
  have hr (i : I) : r i = radicalIndicator (r i) := cost_two_eq_radical (hdegree i) (hcost i)
  have hz (i : I) : r i 0 = 1 := by rw [hr]; exact radicalIndicator_zero _
  have hcard : Fintype.card X = 15 := by
    simp [X, Fintype.card_subtype_compl, Block, Fintype.card_fun, ZMod.card]
  have hbit : ∀ i x, b i x = 0 ∨ b i x = 1 := by
    intro i x
    dsimp [b]
    split_ifs <;> simp
  have hrow : ∀ i, ∑ x, b i x = 3 := by
    intro i
    have hs := sum_nonzero_add_zero (fun x => if IsRadical (r i) x then (1 : ℤ) else 0)
    rw [radical_integer_sum, cost_two_radical_card (hdegree i) (hcost i)] at hs
    simp only [zero_isRadical, if_true] at hs
    change (∑ x, b i x) + 1 = (4 : ℤ) at hs
    omega
  have hdot : ∀ i j, i ≠ j → ∑ x, b i x * b j x = 1 := by
    intro i j hij
    have hs := sum_nonzero_add_zero (fun x =>
      (if IsRadical (r i) x then (1 : ℤ) else 0) * (if IsRadical (r j) x then 1 else 0))
    rw [radical_pair_integer_sum, hpair i j hij] at hs
    simp only [zero_isRadical, if_true, one_mul] at hs
    change (∑ x, b i x * b j x) + 1 = (2 : ℤ) at hs
    omega
  have hcover : ∀ x, ∃ i, b i x = 1 := by
    intro x
    by_contra hn
    have hall : ∀ i, r i x = 0 := by
      intro i
      have hi : ¬ IsRadical (r i) x := by
        intro hi
        apply hn
        exact ⟨i, by simp [b,hi]⟩
      rw [hr]
      simp [radicalIndicator,hi]
    have hc := hconstant x
    simp only [hall,hz,Finset.sum_const_zero,Finset.sum_const,Finset.card_univ,hseven] at hc
    exact (by decide : (0 : F₂) ≠ 7) hc
  obtain ⟨p,hp,hu⟩ := SevenPlaneIncidence.seven_rows_common_point hseven hcard b hbit hrow hdot hcover
  have hiff (i : I) (x : X) : b i x = 1 ↔ IsRadical (r i) x := by simp [b]
  refine ⟨p, fun i => (hiff i p).mp (hp i), ?_⟩
  intro y hy
  exact hu y (fun i => (hiff i y).mpr (hy i))

/-- The pair-intersection hypothesis follows from the actual rank-two pencil
condition, leaving no combinatorial pair data to assume. -/
theorem seven_rank_two_common_radical {I : Type*} [Fintype I]
    (hseven : Fintype.card I = 7) (r : I → Block → F₂)
    (hdegree : ∀ i, HasDegreeLE (r i) 2) (hcost : ∀ i, cost (r i) = 2)
    (hpair : ∀ i j, i ≠ j → (radicalPoints (fun x => r i x + r j x)).card = 4)
    (hconstant : ∀ x, (∑ i, r i x) = ∑ i, r i 0) :
    ∃! p : {x : Block // x ≠ 0}, ∀ i, IsRadical (r i) p := by
  apply seven_cost_two_common_radical hseven r hdegree hcost _ hconstant
  intro i j hij
  exact (pair_radical_geometry (hdegree i) (hdegree j)
    (cost_two_radical_card (hdegree i) (hcost i))
    (cost_two_radical_card (hdegree j) (hcost j)) (hpair i j hij)).1

private theorem sum_coefficient_rows {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hsize : (coefficientRows q).card = 7) (x : Block) :
    (∑ y : coefficientRows q, fiber q y x) = ∑ y : Block, fiber q y x := by
  rw [Finset.sum_coe_sort (coefficientRows q) (fun y => fiber q y x)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y hy hyn
  rw [normalized_no_extra_affine h (by omega) y hyn]
  rfl

/-- With the pairwise rank-two pencil condition supplied, the actual normalized
quartic already has a unique common nonzero radical across all active rows. -/
theorem NormalizedQuartic.common_radical_of_pair_rank_two {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 3)
    (hpair : ∀ y ∈ coefficientRows q, ∀ z ∈ coefficientRows q, y ≠ z →
      (radicalPoints (fun x => fiber q y x + fiber q z x)).card = 4) :
    ∃! p : {x : Block // x ≠ 0}, ∀ y ∈ activeRows q, IsRadical (fiber q y) p := by
  classical
  obtain ⟨hsize,heq,_⟩ := coefficientSpace_dimension_three h.totalDegree h.activeBound hd
  have hs : Fintype.card (coefficientRows q) = 7 := by simpa using hsize
  obtain ⟨p,hp,hu⟩ := seven_rank_two_common_radical hs
    (fun y : coefficientRows q => fiber q y)
    (fun y => h.rowDegree y)
    (fun y => normalized_seven_cost_two h hsize y y.property)
    (fun y z hyz => hpair y y.property z z.property (fun he => hyz (Subtype.ext he)))
    (fun x => by rw [sum_coefficient_rows h hsize, sum_coefficient_rows h hsize]; exact h.sumConstant x)
  refine ⟨p, ?_, ?_⟩
  · intro y hy
    exact hp ⟨y, heq.symm ▸ hy⟩
  · intro z hz
    exact hu z (fun y => hz y (heq ▸ y.property))

/-- Addition of evaluation columns is actual addition of homogeneous row parts. -/
theorem quadraticPart_add_of_code_evaluation {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (y z t : Block)
    (ht : ∀ i, codeBasisWord e i t = codeBasisWord e i y + codeBasisWord e i z) :
    (fun x => quadraticPart q y x + quadraticPart q z x) = quadraticPart q t := by
  funext x
  simp only [quadraticPart_code_expansion e]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ht i, add_mul]

/-- Evaluation-column addition induces addition of the actual row polars. -/
theorem row_sum_polar_of_code_evaluation {q : DoubleBlock → F₂} {d : ℕ}
    (h : NormalizedQuartic q)
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (y z t : Block)
    (ht : ∀ i, codeBasisWord e i t = codeBasisWord e i y + codeBasisWord e i z)
    (x w : Block) :
    polar (fun a => fiber q y a + fiber q z a) x w = polar (fiber q t) x w := by
  rw [polar_add, quadraticPart_polar q y (h.rowDegree y),
    quadraticPart_polar q z (h.rowDegree z), ← polar_add,
    quadraticPart_add_of_code_evaluation e y z t ht,
    ← quadraticPart_polar q t (h.rowDegree t)]

/-- A nonzero evaluation column is equivalent to an active quadratic row. -/
theorem code_column_nonzero_iff {q : DoubleBlock → F₂} {d : ℕ}
    (e : (Fin d → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) (y : Block) :
    (fun i => codeBasisWord e i y) ≠ 0 ↔ y ∈ coefficientRows q := by
  rw [codeBasisWord_detects_rows e y]
  constructor
  · intro hn
    by_contra hz
    apply hn
    funext i
    exact not_ne_iff.mp (fun hi => hz ⟨i,hi⟩)
  · rintro ⟨i,hi⟩ hz
    exact hi (congrFun hz i)

/-- The seven nonzero simplex evaluation columns give a rank-two row at the sum
of every pair of distinct columns. -/
theorem NormalizedQuartic.pair_rank_two_of_simplex_labels {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q) (hsize : (coefficientRows q).card = 7)
    (e : (Fin 3 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q)
    (label : (Fin 3 → F₂) → Block)
    (hl : ∀ v, v ≠ 0 → ∀ y, (fun i => codeBasisWord e i y) = v ↔ y = label v) :
    ∀ y ∈ coefficientRows q, ∀ z ∈ coefficientRows q, y ≠ z →
      (radicalPoints (fun x => fiber q y x + fiber q z x)).card = 4 := by
  intro y hy z hz hyz
  let u : Fin 3 → F₂ := fun i => codeBasisWord e i y
  let v : Fin 3 → F₂ := fun i => codeBasisWord e i z
  have hu : u ≠ 0 := (code_column_nonzero_iff e y).mpr hy
  have hv : v ≠ 0 := (code_column_nonzero_iff e z).mpr hz
  have hune : u ≠ v := by
    intro huv
    have he1 := (hl u hu y).mp rfl
    have he2 := (hl u hu z).mp huv.symm
    exact hyz (he1.trans he2.symm)
  have hw : u + v ≠ 0 := by
    intro he
    apply hune
    have hh := congrArg (fun a => a + v) he
    have hvv : v + v = 0 := by funext i; exact CharTwo.add_self_eq_zero _
    simpa only [add_assoc, hvv, add_zero, zero_add] using hh
  let t := label (u + v)
  have ht : (fun i => codeBasisWord e i t) = u + v := (hl (u+v) hw t).mpr rfl
  have htmem : t ∈ coefficientRows q := (code_column_nonzero_iff e t).mp (by rw [ht]; exact hw)
  have heq : radicalPoints (fun x => fiber q y x + fiber q z x) = radicalPoints (fiber q t) := by
    ext x
    simp only [radicalPoints, Finset.mem_filter, Finset.mem_univ, true_and, IsRadical]
    constructor <;> intro hx w
    · rw [← row_sum_polar_of_code_evaluation h e y z t (fun i => congrFun ht i)]
      exact hx w
    · rw [row_sum_polar_of_code_evaluation h e y z t (fun i => congrFun ht i)]
      exact hx w
  rw [heq]
  exact cost_two_radical_card (h.rowDegree t) (normalized_seven_cost_two h hsize t htmem)

/-- In dimension three, the genuine quadratic coefficient code closes the
rank-two pencil, forcing a unique nonzero common radical of all seven active rows. -/
theorem NormalizedQuartic.common_radical {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 3) :
    ∃! p : {x : Block // x ≠ 0}, ∀ y ∈ activeRows q, IsRadical (fiber q y) p := by
  obtain ⟨e,label,hl,_⟩ := exists_simplex_labels h hd
  have hsize := (coefficientSpace_dimension_three h.totalDegree h.activeBound hd).1
  apply h.common_radical_of_pair_rank_two hd
  exact h.pair_rank_two_of_simplex_labels hsize e label hl

/-- Inactive rows vanish, so the same common radical is valid for every row. -/
theorem NormalizedQuartic.common_radical_all_rows {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 3) :
    ∃! p : {x : Block // x ≠ 0}, ∀ y : Block, IsRadical (fiber q y) p := by
  obtain ⟨p,hp,hu⟩ := h.common_radical hd
  refine ⟨p, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ activeRows q
    · exact hp y hy
    · have hz : fiber q y = 0 := by simpa [activeRows] using hy
      intro x
      simp [hz,polar]
  · intro z hz
    exact hu z (fun y _ => hz y)

#print axioms NormalizedQuartic.common_radical
#print axioms NormalizedQuartic.common_radical_all_rows

end BooleanANF
