import IntegerQuadraticHeight

namespace Astra01.EllipticHeight
noncomputable section
open WeierstrassCurve.Affine.Chart FunctionField.Chart
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

/-- The Cauchy–Schwarz discriminant bound for the actual point height. -/
theorem pointHeight_upper_discriminant (V : WeierstrassCurve.Affine k) [V.IsElliptic]
    (A B : (V.map (algebraMap k K)).Point) (hA : 0 < pointHeight W K _ A) :
    pointHeight W K _ (A-B)-pointHeight W K _ A-pointHeight W K _ B ≤ 0 ∨
      (pointHeight W K _ (A-B)-pointHeight W K _ A-pointHeight W K _ B)^2 ≤
        4*pointHeight W K _ A*pointHeight W K _ B := by
  exact QuadraticHeight.upper_discriminant (pointHeight W K _)
    (pointHeight_parallelogram W K V) (pointHeight_zero W K _)
    (pointHeight_nonneg W K _) A B hA
end
end Astra01.EllipticHeight
#print axioms Astra01.EllipticHeight.pointHeight_upper_discriminant
