import EllipticPrincipalCriterion

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

/-- An actual nonzero rational Weil function for every torsion point.
No principal-divisor criterion is assumed: it follows from the genuine
coordinate-ring class map and the projective product formula. -/
theorem exists_weilFunction (n : ℤ) (T : W.Point) (hT : n • T = 0) :
    ∃ f : W.FunctionFieldˣ,
      EllipticPointDivisor.principalDivisor W W.FunctionField (Additive.ofMul f) =
        Finsupp.single T n - Finsupp.single (0 : W.Point) n := by
  apply principal_of_degree_zero_pointSum_zero
  · simp [Finsupp.sum_sub_index]
  · unfold pointSum
    rw [Finsupp.sum_sub_index (fun _ _ _ => sub_zsmul _ _ _)]
    simp [hT]
end
end Astra01.EllipticPicard
#print axioms Astra01.EllipticPicard.exists_weilFunction
