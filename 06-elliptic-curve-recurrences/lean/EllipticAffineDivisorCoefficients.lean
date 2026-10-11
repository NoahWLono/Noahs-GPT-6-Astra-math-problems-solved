import EllipticAffineClassCriterion

/-! The divisor attached to point ideals has exactly the prescribed finite
point coefficients, including coincident points and arbitrary integer weights. -/
namespace Astra01.EllipticPicard
noncomputable section
open WeierstrassCurve.Affine IsDedekindDomain FractionalIdeal
open Astra01.DedekindDivisor Astra01.EllipticPlaces
open scoped nonZeroDivisors
variable {k : Type*} [Field k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
local instance : DecidableEq k := Classical.decEq _

theorem pointPrime_eq_iff {x y u v : k} (h : W.Nonsingular x y) (j : W.Nonsingular u v) :
    pointPrime W h = pointPrime W j ↔ (Point.some x y h : W.Point) = Point.some u v j := by
  constructor
  · intro hp
    have hi := congrArg HeightOneSpectrum.asIdeal hp
    have hu : CoordinateRing.XYIdeal' (W := W) h = CoordinateRing.XYIdeal' (W := W) j := by
      apply Units.ext
      simpa only [CoordinateRing.XYIdeal'_eq, pointPrime] using
        congrArg (fun I : Ideal W.CoordinateRing =>
          (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) hi
    apply Point.toClass_injective
    rw [Point.toClass_some, Point.toClass_some, hu]
  · intro hp
    obtain ⟨rfl,rfl⟩ := Point.some.inj hp
    rfl

theorem affinePointDivisor_apply (P : W.Point) {x y : k} (h : W.Nonsingular x y) :
    affinePointDivisor W P (pointPrime W h) = if P = Point.some x y h then 1 else 0 := by
  classical
  cases P with
  | zero => simp [affinePointDivisor, pointIdeal, divisor_apply, count_one]
  | some u v j =>
    change count W.FunctionField (pointPrime W h)
      ((pointPrime W j).asIdeal : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = _
    simp only [count_maximal, pointPrime_eq_iff]

theorem affineDivisor_apply (D : W.Point →₀ ℤ) {x y : k} (h : W.Nonsingular x y) :
    affineDivisor W D (pointPrime W h) = D (Point.some x y h) := by
  classical
  simp [affineDivisor, Finsupp.sum, affinePointDivisor_apply, Finsupp.mem_support_iff]
  exact fun h => h.symm
end
end Astra01.EllipticPicard
#print axioms Astra01.EllipticPicard.affineDivisor_apply
