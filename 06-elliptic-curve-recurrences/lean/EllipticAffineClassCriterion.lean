import DivisorClassCriterion
import EllipticFinitePlaces

/-! The actual elliptic point/class-group homomorphism supplies principal
finite-place divisors when the group-weighted point sum vanishes. Infinity
is omitted here and will be recovered using the projective product formula. -/
namespace Astra01.EllipticPicard
noncomputable section
open WeierstrassCurve.Affine IsDedekindDomain FractionalIdeal
open Astra01.DedekindDivisor Astra01.EllipticPlaces
open scoped nonZeroDivisors
variable {k : Type*} [Field k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
local instance : DecidableEq k := Classical.decEq _

def pointIdeal : W.Point → (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ
  | .zero => 1
  | .some _ _ h => CoordinateRing.XYIdeal' h

def affinePointDivisor (P : W.Point) : Divisor W.CoordinateRing := divisor (pointIdeal W P)

def affineDivisor (D : W.Point →₀ ℤ) : Divisor W.CoordinateRing :=
  D.sum fun P z => z • affinePointDivisor W P

def pointSum (D : W.Point →₀ ℤ) : W.Point := D.sum fun P z => z • P

theorem class_affinePointDivisor (P : W.Point) :
    divisorClass (K := W.FunctionField) (affinePointDivisor W P) = Point.toClass P := by
  change (ClassGroup.mk W.FunctionField).toAdditive
    ((divisorEquiv (R := W.CoordinateRing) (K := W.FunctionField)).symm
      ((divisorEquiv (R := W.CoordinateRing) (K := W.FunctionField))
        (Additive.ofMul (pointIdeal W P)))) = _
  rw [AddEquiv.symm_apply_apply]
  cases P <;> simp [pointIdeal, Point.toClass] <;> rfl

theorem class_affineDivisor (D : W.Point →₀ ℤ) :
    divisorClass (K := W.FunctionField) (affineDivisor W D) = Point.toClass (pointSum W D) := by
  simp only [affineDivisor, pointSum, map_finsuppSum, map_zsmul, class_affinePointDivisor]

theorem affine_principal_of_pointSum_zero (D : W.Point →₀ ℤ) (h : pointSum W D = 0) :
    ∃ f : W.FunctionFieldˣ,
      principalDivisor (R := W.CoordinateRing) (Additive.ofMul f) = affineDivisor W D := by
  apply exists_principalDivisor_of_class_zero
  rw [class_affineDivisor, h, map_zero]
end
end Astra01.EllipticPicard
#print axioms Astra01.EllipticPicard.affine_principal_of_pointSum_zero
