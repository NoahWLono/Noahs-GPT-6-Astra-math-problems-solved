import EllipticAffineDivisorCoefficients
import AdicRingEquiv
import EllipticPointResidues

/-! Compatibility of the actual projective point divisor with the coordinate
ring's principal divisor, with normalized valuations (not merely equivalent
valuations). -/
namespace Astra01.EllipticPicard
noncomputable section
attribute [-instance] OreLocalization.instSMulOfIsScalarTower
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticPlaces
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
local instance (priority := 2000) : DecidableEq k := Classical.decEq _
local instance (priority := 2000) : Algebra k[X] W.FunctionField := W.algebraPolynomial W.FunctionField
local instance (priority := 2000) : IsScalarTower k[X] W.CoordinateRing W.FunctionField := W.algebraPolynomial_isScalarTower W.FunctionField
local instance (priority := 2000) : Algebra k⟮X⟯ W.FunctionField := W.algebraRatFunc W.FunctionField
local instance (priority := 2000) : IsScalarTower k[X] k⟮X⟯ W.FunctionField := W.algebraRatFunc_isScalarTower W.FunctionField
local instance (priority := 2000) : _root_.FunctionField k W.FunctionField := W.functionField W.FunctionField
local instance (priority := 2000) : Algebra.IsSeparable k⟮X⟯ W.FunctionField := W.isSeparable W.FunctionField

theorem principalDivisor_finite (f : W.FunctionFieldˣ) {x y : k} (h : W.Nonsingular x y) :
    EllipticPointDivisor.principalDivisor W W.FunctionField (Additive.ofMul f)
      (Point.some x y h) =
    DedekindDivisor.principalDivisor (R := W.CoordinateRing) (Additive.ofMul f)
      (pointPrime W h) := by
  have hv := congrArg (fun v => v (f : W.FunctionField))
    (valuation_ringEquiv (coordinateRingEquivIntegers W W.FunctionField).toRingEquiv
      (EllipticPointDivisor.coordinateIntegers_value W W.FunctionField) (pointPrime W h))
  change placeValuation k W.FunctionField
    (placeOfPoint W W.FunctionField (Point.some x y h)) (f : W.FunctionField) = _ at hv
  have hp := EllipticPointDivisor.point_valuation_eq W W.FunctionField (Additive.ofMul f) (Point.some x y h)
  have hq := FractionalIdeal.valuation_eq_exp_neg_count (pointPrime W h) f
  have hh := hp.symm.trans (hv.trans hq)
  rw [DedekindDivisor.principalDivisor_apply]
  exact neg_injective (WithZero.exp_injective hh)
end
end Astra01.EllipticPicard
#print axioms Astra01.EllipticPicard.principalDivisor_finite
