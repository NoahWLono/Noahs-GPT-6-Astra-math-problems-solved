/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in APACHE-2.0.txt.
Authors: Guanghao Li
The coordinate-ring/integer-ring transport and degree calculation are adapted
from PlaceDictionary.lean, commit dbca5beed1da77e2ecd1eec207d0451fa57e8aa6.
The isolated finite-prime interface and bijective endpoint are local adaptations.
-/
import EllipticInfinity
import EllipticFinitePlaces

namespace WeierstrassCurve.Affine.Chart
noncomputable section
open FunctionField FunctionField.Chart
open Astra01.EllipticPlaces
open scoped RatFunc Polynomial nonZeroDivisors
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

def coordinateRingEquivIntegers : W.CoordinateRing ≃ₐ[k[X]] ringOfIntegers k K :=
  IsIntegralClosure.equiv k[X] W.CoordinateRing K (ringOfIntegers k K)

def finitePlaceOfAffine {x y : k} (h : W.Nonsingular x y) : PlaceA k K :=
  Sum.inl (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (coordinateRingEquivIntegers W K).toRingEquiv (pointPrime W h))

theorem finitePlaceOfAffine_degree {x y : k} (h : W.Nonsingular x y) :
    placeDegree k K (finitePlaceOfAffine W K h) = 1 := by
  let e := coordinateRingEquivIntegers W K
  let I := CoordinateRing.XYIdeal W x (Polynomial.C y)
  let v := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.toRingEquiv (pointPrime W h)
  have hv : v.asIdeal = I.map e.toRingHom := by
    change I.comap e.symm.toRingHom = I.map e.toRingHom
    exact Ideal.comap_symm e.toRingEquiv
  let ek : W.CoordinateRing ≃ₐ[k] ringOfIntegers k K := e.restrictScalars k
  let eqQuot : (W.CoordinateRing ⧸ I) ≃ₐ[k] (ringOfIntegers k K ⧸ v.asIdeal) :=
    Ideal.quotientEquivAlg I v.asIdeal ek hv
  change Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal) = 1
  rw [← eqQuot.toLinearEquiv.finrank_eq]
  exact pointPrime_residue_degree W h

def placeOfPoint : W.Point → PlaceA k K
  | .zero => infinityPlace K
  | .some _ _ h => finitePlaceOfAffine W K h

theorem placeOfPoint_deg_one (P : W.Point) :
    placeDegree k K (placeOfPoint W K P) = 1 := by
  cases P with
  | zero => exact infinityPlace_deg_one W K
  | some x y h => exact finitePlaceOfAffine_degree W K h

theorem placeOfPoint_surjective [IsAlgClosed k] : Function.Surjective (placeOfPoint W K) := by
  intro v
  rcases v with v | v
  · let e := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      (coordinateRingEquivIntegers W K).toRingEquiv
    obtain ⟨x,y,h,heq⟩ := every_finite_prime_is_point W (e.symm v)
    refine ⟨.some x y h, ?_⟩
    change Sum.inl (e (pointPrime W h)) = Sum.inl v
    rw [← heq, Equiv.apply_symm_apply]
  · exact ⟨.zero, congrArg Sum.inr (infinity_heightOne_unique W K _ _)⟩

theorem placeOfPoint_injective : Function.Injective (placeOfPoint W K) := by
  classical
  intro P Q hPQ
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y h => cases hPQ
  | some x y h =>
    cases Q with
    | zero => cases hPQ
    | some u v j =>
      let e := IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
        (coordinateRingEquivIntegers W K).toRingEquiv
      have hp : e (pointPrime W h) = e (pointPrime W j) := Sum.inl.inj hPQ
      have hi := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal (e.injective hp)
      have hu : CoordinateRing.XYIdeal' (W := W) h = CoordinateRing.XYIdeal' (W := W) j := by
        apply Units.ext
        simpa only [CoordinateRing.XYIdeal'_eq, pointPrime] using
          congrArg (fun I : Ideal W.CoordinateRing => (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) hi
      apply Point.toClass_injective
      rw [Point.toClass_some, Point.toClass_some, hu]

def pointPlaceEquiv [IsAlgClosed k] : W.Point ≃ PlaceA k K :=
  Equiv.ofBijective (placeOfPoint W K) ⟨placeOfPoint_injective W K, placeOfPoint_surjective W K⟩

#print axioms pointPlaceEquiv
#print axioms placeOfPoint_deg_one
end
end WeierstrassCurve.Affine.Chart
