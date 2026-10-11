import SharpnessProjectiveAgreements
import EllipticXProjectiveValue

/-! Injective base extension of the sharpness curve's actual elliptic group
and ordinary projective x coordinates. -/
namespace Astra01.SharpnessActual
noncomputable section
open WeierstrassCurve.Affine
open Astra01.EllipticPointDivisor
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
variable (k : Type*) [Field k] [Algebra (ZMod 11) k]
local instance : DecidableEq k := Classical.decEq _

def extendedCurve : WeierstrassCurve.Affine k := curve.map (algebraMap (ZMod 11) k)
instance : (extendedCurve k).IsElliptic := inferInstanceAs
  (curve.map (algebraMap (ZMod 11) k)).IsElliptic

def extendPoint : curve.Point →+ (extendedCurve k).Point :=
  Point.baseChange (W' := curve) (ZMod 11) k

theorem extendPoint_injective : Function.Injective (extendPoint k) :=
  Point.map_injective (W' := curve) (Algebra.ofId (ZMod 11) k)

theorem extended_generator_order : addOrderOf (extendPoint k generator) = 13 := by
  rw [← generator_order]
  exact addOrderOf_injective (extendPoint k) (extendPoint_injective k) generator

theorem extended_xValue (P : curve.Point) :
    coordinateXValue (extendedCurve k) (extendPoint k P) =
      (xValue P).map (algebraMap (ZMod 11) k) := by
  cases P <;> rfl

end
end Astra01.SharpnessActual
#print axioms Astra01.SharpnessActual.extended_generator_order
#print axioms Astra01.SharpnessActual.extended_xValue
