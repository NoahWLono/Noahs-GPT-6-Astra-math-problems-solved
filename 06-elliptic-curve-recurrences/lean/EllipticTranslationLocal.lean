import EllipticPointResidues
import ValuationResidueArithmetic

/-! Translation's induced place map agrees with curve addition wherever the
usual chord denominator is nonzero. Exceptional points are not assumed away
in the final paper goal; extending this local result is a separate next step. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticTranslation
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : DecidableEq k := Classical.decEq _
local instance : DecidableEq K := Classical.decEq _
local instance : (W⁄K).IsElliptic := inferInstanceAs (W.map (algebraMap k K)).IsElliptic

theorem translation_coordinates {u w : k} (hG : W.Nonsingular u w) :
    let e := translationEquiv W K (Point.some u w hG)
    let ℓ := (W⁄K).slope (XK k K) (algebraMap k K u) (W.yCoord K) (algebraMap k K w)
    e (XK k K) = (W⁄K).addX (XK k K) (algebraMap k K u) ℓ ∧
    e (W.yCoord K) = (W⁄K).addY (XK k K) (algebraMap k K u) (W.yCoord K) ℓ := by
  have ht := translationEquiv_generic W K (Point.some u w hG)
  change Point.some ((translationEquiv W K (Point.some u w hG)) (XK k K))
      ((translationEquiv W K (Point.some u w hG)) (W.yCoord K)) _ =
    Point.some (XK k K) (W.yCoord K) _ +
      Point.some (algebraMap k K u) (algebraMap k K w) _ at ht
  rw [Point.add_of_X_ne (generic_x_ne_constant W K u)] at ht
  exact Point.some.inj ht

theorem translation_place_of_x_ne {x y u w : k}
    (hP : W.Nonsingular x y) (hG : W.Nonsingular u w) (hxu : x ≠ u) :
    chartPullbackEquiv (translationEquiv W K (Point.some u w hG))
      (finitePlaceOfAffine W K hP) =
      placeOfPoint W K (Point.some x y hP + Point.some u w hG) := by
  let v := placeValuation k K (finitePlaceOfAffine W K hP)
  letI : v.IsTrivialOn k := Valuation.IsTrivialOn.of_le_one v
    (placeValuation_algebraMap_le_one k K _)
  have hr := finite_point_residues W K hP
  have hx : HasConstantResidue v (XK k K) x := hr.1
  have hy : HasConstantResidue v (W.yCoord K) y := hr.2
  let ℓ := (W⁄K).slope (XK k K) (algebraMap k K u) (W.yCoord K) (algebraMap k K w)
  have hl : HasConstantResidue v ℓ (W.slope x u y w) := by
    dsimp only [ℓ]
    rw [slope_of_X_ne (generic_x_ne_constant W K u), slope_of_X_ne hxu]
    exact (hy.sub (HasConstantResidue.constant w)).div
      (hx.sub (HasConstantResidue.constant u)) (sub_ne_zero.mpr hxu)
  have hax : HasConstantResidue v ((W⁄K).addX (XK k K) (algebraMap k K u) ℓ)
      (W.addX x u (W.slope x u y w)) := by
    exact (((hl.pow 2).add ((HasConstantResidue.constant W.a₁).mul hl)).sub
      (HasConstantResidue.constant W.a₂) |>.sub hx).sub (HasConstantResidue.constant u)
  have hny : HasConstantResidue v ((W⁄K).negAddY (XK k K) (algebraMap k K u) (W.yCoord K) ℓ)
      (W.negAddY x u y (W.slope x u y w)) := by
    exact (hl.mul (hax.sub hx)).add hy
  have hay : HasConstantResidue v ((W⁄K).addY (XK k K) (algebraMap k K u) (W.yCoord K) ℓ)
      (W.addY x u y (W.slope x u y w)) := by
    exact (hny.neg.sub ((HasConstantResidue.constant W.a₁).mul hax)).sub
      (HasConstantResidue.constant W.a₃)
  have he := translation_coordinates W K hG
  dsimp only at he
  rw [Point.add_of_X_ne hxu]
  apply place_eq_of_coordinate_residues W K
  · rw [chartPullback_valuation, map_sub, AlgEquiv.commutes, he.1]
    exact hax
  · rw [chartPullback_valuation, map_sub, AlgEquiv.commutes, he.2]
    exact hay

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.translation_place_of_x_ne
