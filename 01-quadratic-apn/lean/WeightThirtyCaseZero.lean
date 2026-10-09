import AffineGraphFlats
import CoefficientPatterns
import QuadraticFourAffine

namespace BooleanANF
open scoped BigOperators

/-- Cost fourteen permits at most two nonzero affine rows. -/
theorem affine_active_rows_le_two {q : DoubleBlock → F₂}
    (hr : ∀ y, HasDegreeLE (fiber q y) 1)
    (hc : (∑ y : Block, cost (fiber q y)) = 14) : (activeRows q).card ≤ 2 := by
  have hrow (y : Block) : (if fiber q y = 0 then 0 else 6 : ℤ) ≤ cost (fiber q y) := by
    split_ifs with hz
    · rw [hz]
      simp [cost,weight]
    · exact QuadraticFour.affine_nonzero_min_cost (hr y) hz
  have hs := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset Block)) => hrow y)
  rw [hc] at hs
  have he : (∑ y : Block, (if fiber q y = 0 then 0 else 6 : ℤ)) =
      6 * ((activeRows q).card : ℤ) := by
    simp [activeRows, Finset.sum_ite, nsmul_eq_mul, mul_comm]
  rw [he] at hs
  omega

/-- Every x-column is supported on the active y-rows. -/
theorem column_weight_le_active (q : DoubleBlock → F₂) (x : Block) :
    weight (fun y => fiber q y x) ≤ (activeRows q).card := by
  apply weight_le_card_of_supported
  intro y hy
  have hz : fiber q y = 0 := by simpa [activeRows] using hy
  exact congrFun hz x

/-- General cost bookkeeping before using the normalization budget. -/
theorem cost_sum_eq_weight_minus_column (q : DoubleBlock → F₂) :
    (∑ y : Block, cost (fiber q y)) =
      (weight q : ℤ) - 2 * (weight (fun y => fiber q y 0) : ℤ) := by
  simp only [cost, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum]
  rw [show (∑ y : Block, weight (fiber q y)) = weight q from weight_fibers q]
  rfl

/-- Affine rows give total weight divisible by eight. -/
theorem affine_rows_weight_mod_eight {q : DoubleBlock → F₂}
    (hr : ∀ y, HasDegreeLE (fiber q y) 1) : weight q % 8 = 0 := by
  have hw := weight_fibers q
  change (∑ y : Block, weight (fiber q y)) = weight q at hw
  rw [← hw, Finset.sum_nat_mod]
  have hz : ∀ y : Block, weight (fiber q y) % 8 = 0 :=
    fun y => QuadraticFour.affine_weight_mod_eight (hr y)
  simp only [hz, Finset.sum_const_zero, Nat.zero_mod]

/-- In the zero-dimensional code case each x-column has exactly one support point. -/
theorem affine_rows_columns_weight_one {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q) (hr : ∀ y, HasDegreeLE (fiber q y) 1) :
    ∀ x : Block, weight (fun y => fiber q y x) = 1 := by
  have ha := affine_active_rows_le_two hr h.costFourteen
  have hmod := affine_rows_weight_mod_eight hr
  have hcost := cost_sum_eq_weight_minus_column q
  rw [h.costFourteen] at hcost
  have hcol0 := (column_weight_le_active q 0).trans ha
  have hzero : weight (fun y => fiber q y 0) = 1 := by omega
  intro x
  have hcol := (column_weight_le_active q x).trans ha
  have htop : coefficient (fun y => fiber q y x) Finset.univ = 1 := by
    rw [coefficient_top_eq_sum, h.sumConstant x, ← coefficient_top_eq_sum,
      ← weight_cast_eq_top, hzero]
    rfl
  have hodd := weight_odd_of_top_one htop
  change weight (fun y => fiber q y x) % 2 = 1 at hodd
  change weight (fun y => fiber q y x) ≤ 2 at hcol
  omega

/-- The barycenter of a singleton column is its unique support point. -/
def columnPoint (q : DoubleBlock → F₂) (x : Block) : Block :=
  ∑ y : Block, fiber q y x • y

theorem columnPoint_delta {q : DoubleBlock → F₂}
    (hc : ∀ x : Block, weight (fun y => fiber q y x) = 1) (x y : Block) :
    fiber q y x = delta (columnPoint q x) y := by
  obtain ⟨a,ha⟩ := exists_delta_of_weight_one (hc x)
  have hp : columnPoint q x = a := by
    unfold columnPoint
    simp_rw [show ∀ y, fiber q y x = delta a y from congrFun ha]
    simp [delta, ite_smul]
  rw [hp]
  exact congrFun ha y

theorem columnPoint_affine {q : DoubleBlock → F₂}
    (hr : ∀ y, HasDegreeLE (fiber q y) 1) (i : Fin 4) :
    HasDegreeLE (fun x => columnPoint q x i) 1 := by
  have he : (fun x => columnPoint q x i) =
      fun x => ∑ y : Block, y i * fiber q y x := by
    funext x
    simp [columnPoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [he]
  apply HasDegreeLE.sum
  intro y hy
  exact (hr y).smul (y i)

/-- Case d=0: the residual is an affine graph, so the signal is two transverse flats. -/
theorem weight_thirty_case_zero {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hD : quadraticCoefficientSpace q = ⊥) : TwoTransverseFlats (residualSignal q) := by
  have hr := affine_rows_of_coefficientSpace_zero h.rowDegree hD
  have hc := affine_rows_columns_weight_one h hr
  obtain ⟨L,hL⟩ := exists_linear_part (columnPoint q) (columnPoint_affine hr)
  apply affine_graph_two_flats q (columnPoint q 0) L
  intro x y
  rw [← hL x]
  exact columnPoint_delta hc x y


theorem weight_thirty_case_zero_finrank {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 0) :
    TwoTransverseFlats (residualSignal q) :=
  weight_thirty_case_zero h (Submodule.finrank_eq_zero.mp hd)

end BooleanANF
