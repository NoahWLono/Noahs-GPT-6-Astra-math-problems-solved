import EllipticXYDegrees

namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open scoped RatFunc Polynomial Polynomial.Bivariate
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : DecidableEq k := Classical.decEq _

theorem infinity_valuation_x :
    placeValuation k K (placeOfPoint W K 0) (XK k K) = WithZero.exp 2 := by
  have hd : (-(principalDivisor W K (Additive.ofMul (xCoordinateUnit W K)) 0)).toNat = 2 := by
    simpa only [poleDivisor, Finsupp.mapRange_apply, Finsupp.single_eq_same] using
      congrArg (fun d => d 0) (poleDivisor_x W K)
  have hi : -(principalDivisor W K (Additive.ofMul (xCoordinateUnit W K)) 0) = 2 := by omega
  have hv := point_valuation_eq W K (Additive.ofMul (xCoordinateUnit W K)) 0
  rw [hi] at hv
  exact hv

theorem infinity_valuation_y :
    placeValuation k K (placeOfPoint W K 0) (W.yCoord K) = WithZero.exp 3 := by
  have hd : (-(principalDivisor W K (Additive.ofMul (yCoordinateUnit W K)) 0)).toNat = 3 := by
    simpa only [poleDivisor, Finsupp.mapRange_apply, Finsupp.single_eq_same] using
      congrArg (fun d => d 0) (poleDivisor_y W K)
  have hi : -(principalDivisor W K (Additive.ofMul (yCoordinateUnit W K)) 0) = 3 := by omega
  have hv := point_valuation_eq W K (Additive.ofMul (yCoordinateUnit W K)) 0
  rw [hi] at hv
  exact hv

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.infinity_valuation_x
#print axioms Astra01.EllipticPointDivisor.infinity_valuation_y
