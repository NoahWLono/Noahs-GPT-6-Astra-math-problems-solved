import EllipticPrincipalCriterion

/-! The vertical-line divisor from Mathlib's genuine point-ideal identity. -/
namespace Astra01.EllipticPicard
noncomputable section
attribute [-instance] OreLocalization.instSMulOfIsScalarTower
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticPlaces
open scoped RatFunc Polynomial nonZeroDivisors
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
local instance (priority := 2000) : DecidableEq k := Classical.decEq _
local instance (priority := 2000) : Algebra k[X] W.FunctionField := W.algebraPolynomial W.FunctionField
local instance (priority := 2000) : IsScalarTower k[X] W.CoordinateRing W.FunctionField := W.algebraPolynomial_isScalarTower W.FunctionField
local instance (priority := 2000) : Algebra k⟮X⟯ W.FunctionField := W.algebraRatFunc W.FunctionField
local instance (priority := 2000) : IsScalarTower k[X] k⟮X⟯ W.FunctionField := W.algebraRatFunc_isScalarTower W.FunctionField
local instance (priority := 2000) : _root_.FunctionField k W.FunctionField := W.functionField W.FunctionField
local instance (priority := 2000) : Algebra.IsSeparable k⟮X⟯ W.FunctionField := W.isSeparable W.FunctionField

def xDifferenceUnit (x : k) : W.FunctionFieldˣ :=
  Units.mk0 (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x))
    (by simpa using ((IsFractionRing.injective W.CoordinateRing W.FunctionField).ne
      (CoordinateRing.XClass_ne_zero x)))

theorem xDifference_principalIdeal {x y : k} (h : W.Nonsingular x y) :
    DedekindDivisor.principalIdeal (R := W.CoordinateRing) (xDifferenceUnit W x) =
      pointIdeal W (-(Point.some x y h : W.Point)) * pointIdeal W (Point.some x y h) := by
  apply Units.ext
  change FractionalIdeal.spanSingleton W.CoordinateRing⁰
    (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)) =
      (CoordinateRing.XYIdeal W x (Polynomial.C (W.negY x y)) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField) *
      (CoordinateRing.XYIdeal W x (Polynomial.C y) :
        FractionalIdeal W.CoordinateRing⁰ W.FunctionField)
  rw [← FractionalIdeal.coeIdeal_mul, CoordinateRing.XYIdeal_neg_mul h,
    CoordinateRing.XIdeal, FractionalIdeal.coeIdeal_span_singleton]

theorem xDifference_affine_divisor {x y : k} (h : W.Nonsingular x y) :
    DedekindDivisor.principalDivisor (R := W.CoordinateRing)
      (Additive.ofMul (xDifferenceUnit W x)) =
      affinePointDivisor W (-(Point.some x y h : W.Point)) +
        affinePointDivisor W (Point.some x y h) := by
  change DedekindDivisor.divisorEquiv
    (Additive.ofMul (DedekindDivisor.principalIdeal (xDifferenceUnit W x))) = _
  rw [xDifference_principalIdeal W h]
  exact map_add DedekindDivisor.divisorEquiv _ _

private theorem divisor_eq_of_finite_and_sum (A B : W.Point →₀ ℤ)
    (hA : A.sum (fun _ n => n) = 0) (hB : B.sum (fun _ n => n) = 0)
    (hfin : ∀ {x y : k} (h : W.Nonsingular x y),
      A (Point.some x y h) = B (Point.some x y h)) : A = B := by
  classical
  have he : A - B = Finsupp.single (0 : W.Point) ((A - B) 0) := by
    ext P
    cases P with
    | zero => change (A - B) 0 = (Finsupp.single (0 : W.Point) ((A - B) 0)) 0
              simp only [Finsupp.single_eq_same]
    | some x y h => simp [hfin h]
  have hz : (A - B).sum (fun _ n => n) = 0 := by
    rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), hA, hB, sub_self]
  rw [he] at hz
  simp only [Finsupp.sum_single_index] at hz
  apply sub_eq_zero.mp
  rw [he, hz, Finsupp.single_zero]

/-- Exact vertical-line divisor, including 2-torsion points where P=−P. -/
theorem xDifference_projective_divisor {x y : k} (h : W.Nonsingular x y) :
    EllipticPointDivisor.principalDivisor W W.FunctionField
      (Additive.ofMul (xDifferenceUnit W x)) =
      Finsupp.single (Point.some x y h : W.Point) 1 +
        Finsupp.single (-(Point.some x y h : W.Point)) 1 -
        Finsupp.single (0 : W.Point) 2 := by
  classical
  apply divisor_eq_of_finite_and_sum W
  · exact EllipticPointDivisor.sum_principalDivisor_eq_zero W W.FunctionField _
  · simp [Finsupp.sum_sub_index, Finsupp.sum_add_index]
  · intro u v j
    rw [principalDivisor_finite, xDifference_affine_divisor W h]
    simp [affinePointDivisor_apply, Finsupp.single_apply, eq_comm, add_comm]

end
end Astra01.EllipticPicard
#print axioms Astra01.EllipticPicard.xDifference_affine_divisor

#print axioms Astra01.EllipticPicard.xDifference_projective_divisor
