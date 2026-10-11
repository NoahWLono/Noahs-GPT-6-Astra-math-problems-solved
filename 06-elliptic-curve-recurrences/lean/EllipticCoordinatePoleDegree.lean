import GlobalProjectiveRecurrence

/-! Actual pole degree of a regular affine-coordinate-ring function, derived
from its quadratic norm and the unique infinity place. This is the coordinate
degree bridge needed by the paper's sharpness and semiconjugacy examples. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open scoped RatFunc Polynomial nonZeroDivisors
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : DecidableEq k := Classical.decEq _

theorem principal_at_infinity_eq_neg_norm_degree (f : Kˣ) :
    principalDivisor W K (Additive.ofMul f) 0 =
      -(Algebra.norm k⟮X⟯ (f : K)).intDegree := by
  classical
  let v := infinityHeightOne (k := k) K
  let d := Astra01.DedekindDivisor.principalDivisor
    (R := infiniteIntegers k K) (K := K) (Additive.ofMul f)
  have hd : d = Finsupp.single v (d v) := by
    ext w
    have hw : w = v := infinity_heightOne_unique W K w v
    subst w
    simp
  have ht := infinitePrincipalDegree_eq_neg_intDegree_norm k K f
  change d.sum (fun w n => n * (placeDegree k K (Sum.inr w) : ℤ)) = _ at ht
  have hdeg : placeDegree k K (Sum.inr v) = 1 := infinityPlace_deg_one W K
  rw [hd, Finsupp.sum_single_index (by simp), hdeg, Nat.cast_one, mul_one] at ht
  rw [principalDivisor_apply]
  change principalDivisorA k K (Additive.ofMul f) (Sum.inr v) = _
  rw [principalDivisorA_apply_infinite]
  exact ht

theorem coordinate_finite_valuation_le_one (r : W.CoordinateRing) {x y : k}
    (hP : W.Nonsingular x y) :
    placeValuation k K (placeOfPoint W K (Point.some x y hP))
      (algebraMap W.CoordinateRing K r) ≤ 1 := by
  let v := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (coordinateRingEquivIntegers W K).toRingEquiv (Astra01.EllipticPlaces.pointPrime W hP)
  rw [← coordinateIntegers_value W K r]
  exact v.valuation_le_one (coordinateRingEquivIntegers W K r)

theorem poleDivisor_coordinate (r : W.CoordinateRing) (f : Kˣ)
    (hf : (f : K) = algebraMap W.CoordinateRing K r) :
    poleDivisor W K f = Finsupp.single 0 (Algebra.norm k⟮X⟯ (f : K)).intDegree.toNat := by
  classical
  ext P
  cases P with
  | zero =>
    change (-principalDivisor W K (Additive.ofMul f) 0).toNat =
      (Finsupp.single (0 : W.Point) (Algebra.norm k⟮X⟯ (f : K)).intDegree.toNat) 0
    simp only [poleDivisor, Finsupp.mapRange_apply, Finsupp.single_eq_same,
      principal_at_infinity_eq_neg_norm_degree, neg_neg]
  | some x y hP =>
    have hv := coordinate_finite_valuation_le_one W K r hP
    rw [← hf, point_valuation_unit W K f (Point.some x y hP), ← WithZero.exp_zero] at hv
    have hd := WithZero.exp_le_exp.mp hv
    simp only [poleDivisor, Finsupp.mapRange_apply, Finsupp.single_apply]
    simp only [show (0 : W.Point) ≠ Point.some x y hP from (Point.some_ne_zero hP).symm, if_false]
    omega

theorem field_norm_coordinate (r : W.CoordinateRing) :
    Algebra.norm k⟮X⟯ (algebraMap W.CoordinateRing K r) =
      algebraMap k[X] k⟮X⟯ (Algebra.norm k[X] r) := by
  have h := Algebra.intNorm_eq_of_isLocalization k[X]⁰ (Aₘ := k⟮X⟯) (Bₘ := K) r
  rw [Algebra.intNorm_eq_norm k[X] W.CoordinateRing, Algebra.intNorm_eq_norm k⟮X⟯ K] at h
  exact h.symm

/-- The pole degree of an actual affine coordinate-ring element is the
polynomial degree of its quadratic norm, with no assumed valuation at infinity. -/
theorem pole_degree_coordinate (r : W.CoordinateRing) (f : Kˣ)
    (hf : (f : K) = algebraMap W.CoordinateRing K r) :
    divisorDegree W (poleDivisor W K f) = (Algebra.norm k[X] r).natDegree := by
  rw [poleDivisor_coordinate W K r f hf]
  unfold divisorDegree
  rw [Finsupp.sum_single_index (by rfl)]
  rw [hf, field_norm_coordinate W K r, RatFunc.intDegree_polynomial]
  simp

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.pole_degree_coordinate
