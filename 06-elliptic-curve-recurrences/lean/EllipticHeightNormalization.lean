import EllipticHeightParallelogram
import EllipticXYDegrees

/-! Positivity and pole-degree normalization of the actual point height. -/
namespace Astra01.EllipticHeight
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField.Chart
open Astra01.EllipticPointDivisor
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq K := Classical.decEq _

variable (V : WeierstrassCurve.Affine K)

theorem pointDivisor_nonneg (A : V.Point) (P : W.Point) : 0 ≤ pointDivisor W K V A P := by
  have hb := (vectorDivisor_valuation W K A.xRep A.xRep_ne_zero P).1
  have hi : 1 ≤ WithZero.exp (pointDivisor W K V A P) := by
    cases A with
    | zero => simpa [pointDivisor, WeierstrassCurve.Affine.Point.xRep] using hb (0 : Fin 2)
    | some x y h => simpa [pointDivisor, WeierstrassCurve.Affine.Point.xRep] using hb (1 : Fin 2)
  exact WithZero.exp_le_exp.mp (by simpa only [WithZero.exp_zero] using hi)

theorem pointHeight_nonneg (A : V.Point) : 0 ≤ pointHeight W K V A := by
  change 0 ≤ (pointDivisor W K V A).sum (fun _ n => n)
  exact Finsupp.sum_nonneg' fun P => pointDivisor_nonneg W K V A P

theorem pointDivisor_zero : pointDivisor W K V 0 = 0 := by
  ext P
  apply vectorDivisor_eq_of_bounds
  · intro i
    fin_cases i <;> simp [WeierstrassCurve.Affine.Point.xRep]
  · exact ⟨0, by simp [WeierstrassCurve.Affine.Point.xRep]⟩

theorem pointHeight_zero : pointHeight W K V 0 = 0 := by
  change (pointDivisor W K V 0).sum (fun _ n => n) = 0
  rw [pointDivisor_zero]
  rfl

theorem pointHeight_neg (A : V.Point) : pointHeight W K V (-A) = pointHeight W K V A := by
  unfold pointHeight
  simp only [WeierstrassCurve.Affine.Point.xRep_neg]

theorem pointDivisor_some {x y : K} (h : V.Nonsingular x y) (hx : x ≠ 0) :
    pointDivisor W K V (WeierstrassCurve.Affine.Point.some x y h) =
      (poleDivisor W K (Units.mk0 x hx)).mapRange (fun n : ℕ => (n : ℤ)) (by rfl) := by
  classical
  ext P
  apply WithZero.exp_injective
  change WithZero.exp (vectorDivisor W K _ _ P) = _
  rw [exp_vectorDivisor]
  have h2 : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
  simp only [WeierstrassCurve.Affine.Point.xRep_some, h2, Finset.sup_insert,
    Finset.sup_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    map_one, Finsupp.mapRange_apply, poleDivisor]
  have hv := point_valuation_unit W K (Units.mk0 x hx) P
  change placeValuation k K (placeOfPoint W K P) x = _ at hv
  rw [hv]
  set d := principalDivisor W K (Additive.ofMul (Units.mk0 x hx)) P
  change max (WithZero.exp (-d)) 1 = WithZero.exp (((-d).toNat : ℕ) : ℤ)
  by_cases hd : 0 ≤ -d
  · rw [max_eq_left (by simpa only [WithZero.exp_zero] using WithZero.exp_le_exp.mpr hd),
      Int.toNat_of_nonneg hd]
  · have hd' : -d ≤ 0 := le_of_not_ge hd
    rw [max_eq_right (by simpa only [WithZero.exp_zero] using WithZero.exp_le_exp.mpr hd'),
      Int.toNat_of_nonpos hd', Nat.cast_zero, WithZero.exp_zero]

theorem pointHeight_some {x y : K} (h : V.Nonsingular x y) (hx : x ≠ 0) :
    pointHeight W K V (WeierstrassCurve.Affine.Point.some x y h) =
      (divisorDegree W (poleDivisor W K (Units.mk0 x hx)) : ℤ) := by
  classical
  change (pointDivisor W K V _).sum (fun _ n => n) = _
  rw [pointDivisor_some W K V h hx, Finsupp.sum_mapRange_index (fun _ => rfl)]
  simp only [divisorDegree, Finsupp.sum, Nat.cast_sum]

/-- The genuine generic point has x-height two. -/
theorem generic_point_height :
    pointHeight W K (W⁄K) (EllipticTranslation.genericPoint W K) = 2 := by
  unfold EllipticTranslation.genericPoint
  rw [pointHeight_some W K _ _ (xCoord_ne_zero W K)]
  change (divisorDegree W (poleDivisor W K (xCoordinateUnit W K)) : ℤ) = 2
  rw [pole_degree_x]
  rfl

end
end Astra01.EllipticHeight
#print axioms Astra01.EllipticHeight.pointHeight_nonneg
#print axioms Astra01.EllipticHeight.pointHeight_zero
#print axioms Astra01.EllipticHeight.pointHeight_some

#print axioms Astra01.EllipticHeight.generic_point_height
