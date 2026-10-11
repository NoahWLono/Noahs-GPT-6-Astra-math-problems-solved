import EllipticAutomorphismDivisor
import EllipticTranslation

/-! The actual point/place dictionary is characterized by the residues of x and y.
This is the local interface used to identify translation's induced place action. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticPlaces
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : IsScalarTower k W.CoordinateRing K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing,
      ← IsScalarTower.algebraMap_apply k[X] W.CoordinateRing K]

theorem coordinateIntegers_value (r : W.CoordinateRing) :
    algebraMap (ringOfIntegers k K) K (coordinateRingEquivIntegers W K r) =
      algebraMap W.CoordinateRing K r := IsIntegralClosure.algebraMap_equiv _ _ _ _ r

theorem xDifference_value (c : k) :
    algebraMap (ringOfIntegers k K) K
      (coordinateRingEquivIntegers W K (CoordinateRing.XClass W c)) =
      XK k K - algebraMap k K c := by
  rw [coordinateIntegers_value]
  simp only [CoordinateRing.XClass, map_sub]
  rw [xCoord_eq_XK W K]
  congr 1
  exact (IsScalarTower.algebraMap_apply k W.CoordinateRing K c).symm

theorem yDifference_value (c : k) :
    algebraMap (ringOfIntegers k K) K
      (coordinateRingEquivIntegers W K (CoordinateRing.YClass W (Polynomial.C c))) =
      W.yCoord K - algebraMap k K c := by
  rw [coordinateIntegers_value]
  simp only [CoordinateRing.YClass, map_sub]
  congr 1
  exact (IsScalarTower.algebraMap_apply k W.CoordinateRing K c).symm

theorem finite_point_residues {x y : k} (h : W.Nonsingular x y) :
    placeValuation k K (finitePlaceOfAffine W K h) (XK k K - algebraMap k K x) < 1 ∧
    placeValuation k K (finitePlaceOfAffine W K h) (W.yCoord K - algebraMap k K y) < 1 := by
  let e := coordinateRingEquivIntegers W K
  let v := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv (pointPrime W h)
  constructor
  · rw [← xDifference_value W K]
    change v.valuation K (algebraMap (ringOfIntegers k K) K (e (CoordinateRing.XClass W x))) < 1
    apply (v.valuation_lt_one_iff_mem (K := K) _).mpr
    change e.symm (e (CoordinateRing.XClass W x)) ∈ CoordinateRing.XYIdeal W x (Polynomial.C y)
    rw [AlgEquiv.symm_apply_apply]
    exact Ideal.subset_span (Set.mem_insert _ _)
  · rw [← yDifference_value W K]
    change v.valuation K (algebraMap (ringOfIntegers k K) K (e (CoordinateRing.YClass W (Polynomial.C y)))) < 1
    apply (v.valuation_lt_one_iff_mem (K := K) _).mpr
    change e.symm (e (CoordinateRing.YClass W (Polynomial.C y))) ∈ CoordinateRing.XYIdeal W x (Polynomial.C y)
    rw [AlgEquiv.symm_apply_apply]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem place_eq_of_coordinate_residues (v : PlaceA k K) {x y : k} (h : W.Nonsingular x y)
    (hx : placeValuation k K v (XK k K - algebraMap k K x) < 1)
    (hy : placeValuation k K v (W.yCoord K - algebraMap k K y) < 1) :
    v = finitePlaceOfAffine W K h := by
  cases v with
  | inr v =>
    have hxle : v.valuation K (XK k K) ≤ 1 := by
      rw [← sub_add_cancel (XK k K) (algebraMap k K x)]
      exact (v.valuation K).map_add_le hx.le
        (placeValuation_algebraMap_le_one k K (Sum.inr v) x)
    exact False.elim ((not_le_of_gt (FunctionField.Place.infinite_X_gt_one k K v)) hxle)
  | inl v =>
    let e := coordinateRingEquivIntegers W K
    let u := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv (pointPrime W h)
    have hu : u.asIdeal = (pointPrime W h).asIdeal.map e.toRingHom := Ideal.comap_symm e.toRingEquiv
    have hle : u.asIdeal ≤ v.asIdeal := by
      rw [hu]
      apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.span_le.mpr
      intro z hz
      rcases hz with rfl | hz
      · change e (CoordinateRing.XClass W x) ∈ v.asIdeal
        apply (v.valuation_lt_one_iff_mem (K := K) _).mp
        change v.valuation K (algebraMap (ringOfIntegers k K) K
          (coordinateRingEquivIntegers W K (CoordinateRing.XClass W x))) < 1
        rw [xDifference_value W K]
        exact hx
      · rcases hz with rfl
        change e (CoordinateRing.YClass W (Polynomial.C y)) ∈ v.asIdeal
        apply (v.valuation_lt_one_iff_mem (K := K) _).mp
        change v.valuation K (algebraMap (ringOfIntegers k K) K
          (coordinateRingEquivIntegers W K (CoordinateRing.YClass W (Polynomial.C y)))) < 1
        rw [yDifference_value W K]
        exact hy
    have he : u = v := IsDedekindDomain.HeightOneSpectrum.ext
      ((u.isPrime.isMaximal u.ne_bot).eq_of_le v.isPrime.ne_top hle)
    exact congrArg Sum.inl he.symm

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.place_eq_of_coordinate_residues
