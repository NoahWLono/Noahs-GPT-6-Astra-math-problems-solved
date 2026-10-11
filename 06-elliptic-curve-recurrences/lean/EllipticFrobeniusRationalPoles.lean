import EllipticFrobeniusInfinity
import GlobalRecurrenceObstruction

namespace Astra01.EllipticFrobenius
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField.Chart
open Astra01.EllipticHeight Astra01.EllipticTranslation
open scoped RatFunc Polynomial
variable {F k : Type*} [Field F] [Fintype F] [Field k] [IsAlgClosed k] [Algebra F k]
variable (V : WeierstrassCurve.Affine F) [V.IsElliptic]
local instance : (V⁄k).IsElliptic := inferInstanceAs (V.map (algebraMap F k)).IsElliptic
variable (K : Type*) [Field K] [Algebra (V⁄k).CoordinateRing K]
  [IsFractionRing (V⁄k).CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] (V⁄k).CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : DecidableEq F := Classical.decEq _
local instance : DecidableEq k := Classical.decEq _
local instance : DecidableEq K := Classical.decEq _

open Astra01.EllipticPointDivisor Astra01.EllipticAddSub

theorem geometricDifferenceX_ne_zero : geometricDifferenceX (k := k) V K ≠ 0 := by
  intro h
  have hv := geometricDifferenceX_infinity (k := k) V K
  rw [h,map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

def geometricDifferenceUnit : Kˣ :=
  Units.mk0 (geometricDifferenceX (k := k) V K) (geometricDifferenceX_ne_zero (k := k) V K)

theorem geometricDifference_pole_zero :
    poleDivisor (V⁄k) K (geometricDifferenceUnit (k := k) V K) 0 = 2 := by
  have hv := point_valuation_eq (V⁄k) K (Additive.ofMul (geometricDifferenceUnit (k := k) V K)) 0
  have he := geometricDifferenceX_infinity (k := k) V K
  have hi := WithZero.exp_injective (hv.symm.trans he)
  change (-(principalDivisor (V⁄k) K (Additive.ofMul (geometricDifferenceUnit (k := k) V K)) 0)).toNat = 2
  rw [hi]
  rfl

theorem geometricDifferenceX_translation (T : (V⁄F).Point) :
    translationEquiv (V⁄k) K (Point.baseChange F k T) (geometricDifferenceX (k := k) V K) =
      geometricDifferenceX (k := k) V K := by
  letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra
  letI : IsScalarTower F k K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨y,hy,hpoint⟩ := geometricDifference_some (k := k) V K
  have ht := geometricDifference_translation (k := k) V K T
  rw [hpoint,Point.map_some,Point.some.injEq] at ht
  exact ht.1

theorem geometricDifference_pole_rational (T : (V⁄F).Point) :
    poleDivisor (V⁄k) K (geometricDifferenceUnit (k := k) V K) (Point.baseChange F k T) = 2 := by
  have he : Units.map (translationEquiv (V⁄k) K (Point.baseChange F k T)).toMonoidHom
      (geometricDifferenceUnit (k := k) V K) = geometricDifferenceUnit (k := k) V K := by
    apply Units.ext
    exact geometricDifferenceX_translation (k := k) V K T
  have h := poleDivisor_translation (V⁄k) K (Point.baseChange F k T) 0
    (geometricDifferenceUnit (k := k) V K)
  rw [he,zero_add,geometricDifference_pole_zero] at h
  exact h.symm

end
end Astra01.EllipticFrobenius
#print axioms Astra01.EllipticFrobenius.geometricDifferenceX_translation
#print axioms Astra01.EllipticFrobenius.geometricDifference_pole_rational
