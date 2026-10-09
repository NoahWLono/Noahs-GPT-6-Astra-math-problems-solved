import WeightThirtyCaseZero
import QuadraticFourMoments

namespace BooleanANF
open scoped BigOperators

theorem weight_columns (q : DoubleBlock → F₂) :
    (∑ x : Block, weight (fun y => fiber q y x)) = weight q := by
  change (∑ x : Block, ∑ y : Block, (fiber q y x).val) = weight q
  rw [Finset.sum_comm]
  exact weight_fibers q

theorem columnPoint_degree {q : DoubleBlock → F₂} {d : ℕ}
    (hr : ∀ y, HasDegreeLE (fiber q y) d) (i : Fin 4) :
    HasDegreeLE (fun x => columnPoint q x i) d := by
  have he : (fun x => columnPoint q x i) =
      fun x => ∑ y : Block, y i * fiber q y x := by
    funext x
    simp [columnPoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [he]
  apply HasDegreeLE.sum
  intro y hy
  exact (hr y).smul (y i)

/-- Vanishing first moments kill every quadratic coefficient of the singleton-column map. -/
theorem columnPoint_affine_of_quartic {q : DoubleBlock → F₂}
    (hq : HasDegreeLE q 4) (hr : ∀ y, HasDegreeLE (fiber q y) 2) (i : Fin 4) :
    HasDegreeLE (fun x => columnPoint q x i) 1 := by
  intro s hs
  by_cases hc : s.card = 2
  · have hd : HasDegreeLE (fiberCoefficient q s) 2 :=
      HasDegreeLE.fiberCoefficient (d := 2) (e := 2) hq s (by omega)
    have hm := congrFun (QuadraticFour.quadratic_first_moment_zero hd) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hm
    have he : (fun x => columnPoint q x i) =
        fun x => ∑ y : Block, y i * fiber q y x := by
      funext x
      simp [columnPoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [he, coefficient_sum]
    simp_rw [coefficient_smul]
    change (∑ y : Block, y i * fiberCoefficient q s y) = 0
    simpa only [mul_comm] using hm
  · exact columnPoint_degree hr i s (by omega)

/-- Cost fourteen, constant column parity and total weight sixteen force singleton columns. -/
theorem weight_sixteen_columns_one {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q) (hw : weight q = 16) :
    ∀ x : Block, weight (fun y => fiber q y x) = 1 := by
  have hc := cost_sum_eq_weight_minus_column q
  rw [h.costFourteen, hw] at hc
  have hzero : weight (fun y => fiber q y 0) = 1 := by omega
  have hodd (x : Block) : weight (fun y => fiber q y x) % 2 = 1 := by
    apply weight_odd_of_top_one
    rw [coefficient_top_eq_sum, h.sumConstant x, ← coefficient_top_eq_sum,
      ← weight_cast_eq_top, hzero]
    rfl
  have hpos (x : Block) : (1 : ℤ) ≤ (weight (fun y => fiber q y x) : ℤ) := by
    have ho := hodd x
    omega
  have hsum : (∑ x : Block, (weight (fun y => fiber q y x) : ℤ)) = 16 := by
    rw [← Nat.cast_sum, weight_columns, hw]
    rfl
  have hdiff : (∑ x : Block, ((weight (fun y => fiber q y x) : ℤ) - 1)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    norm_num [Block, Fintype.card_fun, ZMod.card]
  intro x
  have ht := Finset.single_le_sum
    (fun z (_ : z ∈ (Finset.univ : Finset Block)) => sub_nonneg.mpr (hpos z))
    (Finset.mem_univ x)
  rw [hdiff] at ht
  have hp := hpos x
  omega

/-- Common geometric closure for d=0 and d=1: a weight-sixteen residual is an affine graph. -/
theorem weight_thirty_graph_of_weight_sixteen {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q) (hw : weight q = 16) :
    TwoTransverseFlats (residualSignal q) := by
  have hc := weight_sixteen_columns_one h hw
  obtain ⟨L,hL⟩ := exists_linear_part (columnPoint q)
    (columnPoint_affine_of_quartic h.totalDegree h.rowDegree)
  apply affine_graph_two_flats q (columnPoint q 0) L
  intro x y
  rw [← hL x]
  exact columnPoint_delta hc x y

end BooleanANF
