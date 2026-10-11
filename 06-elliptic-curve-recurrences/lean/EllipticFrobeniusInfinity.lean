import EllipticFrobeniusGeneric
import EllipticChordPole
import EllipticCoordinateInfinityValuation

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

def geometricDifferenceX : K :=
  ((V⁄k)⁄K).addX (XK k K) ((XK k K)^Fintype.card F)
    (((V⁄k)⁄K).slope (XK k K) ((XK k K)^Fintype.card F) ((V⁄k).yCoord K)
      (((V⁄k)⁄K).negY ((XK k K)^Fintype.card F) (((V⁄k).yCoord K)^Fintype.card F)))

theorem geometricDifferenceX_infinity :
    placeValuation k K (placeOfPoint (V⁄k) K 0) (geometricDifferenceX (k := k) V K) = WithZero.exp 2 := by
  letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra
  let v := placeValuation k K (placeOfPoint (V⁄k) K 0)
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hx := infinity_valuation_x (V⁄k) K
  have hy := infinity_valuation_y (V⁄k) K
  have hxq : v ((XK k K)^Fintype.card F) = WithZero.exp (2*(Fintype.card F : ℤ)) := by
    rw [map_pow,hx,← WithZero.exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hyq : v (((V⁄k).yCoord K)^Fintype.card F) = WithZero.exp (3*(Fintype.card F : ℤ)) := by
    rw [map_pow,hy,← WithZero.exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hc (c : k) : v (algebraMap k K c) ≤ 1 :=
    placeValuation_algebraMap_le_one k K (placeOfPoint (V⁄k) K 0) c
  have hcs : v (V⁄K).a₁ ≤ 1 ∧ v (V⁄K).a₂ ≤ 1 ∧ v (V⁄K).a₃ ≤ 1 ∧
      v (V⁄K).a₄ ≤ 1 ∧ v (V⁄K).a₆ ≤ 1 := ⟨hc _,hc _,hc _,hc _,hc _⟩
  have hbase : (V⁄K).Nonsingular (XK k K) ((V⁄k).yCoord K) :=
    (((V⁄k)⁄K).equation_iff_nonsingular).mp (yCoord_equation (V⁄k) K)
  have hpow : (V⁄K).Nonsingular ((XK k K)^Fintype.card F)
      (((V⁄k).yCoord K)^Fintype.card F) :=
    (V.baseChange_nonsingular (FiniteField.frobeniusAlgHom F K).injective ..).mpr hbase
  have hneg := (WeierstrassCurve.Affine.nonsingular_neg ..).mpr hpow
  have hn := negY_valuation v (V⁄K) hcs.1 hcs.2.2.1 (Fintype.card F)
    (by exact_mod_cast (show 1 ≤ Fintype.card F by omega)) hxq hyq
  exact addX_valuation v (V⁄K) hcs (Fintype.card F) (by exact_mod_cast hq)
    hbase.1 hneg.1 hx hxq hy hn

include V in
theorem generic_x_ne_frobenius_x : XK k K ≠ (XK k K)^Fintype.card F := by
  intro h
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have he := congrArg (placeValuation k K (placeOfPoint (V⁄k) K 0)) h
  rw [map_pow,infinity_valuation_x,← WithZero.exp_nsmul] at he
  have hi := WithZero.exp_injective he
  simp only [nsmul_eq_mul] at hi
  omega

/-- The explicit pole function is the actual x coordinate of generic minus Frobenius. -/
theorem geometricDifference_some :
    letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra;
    ∃ (y : K) (h : (V⁄K).Nonsingular (geometricDifferenceX (k := k) V K) y),
      geometricGeneric V K - pointFrobenius V K (geometricGeneric V K) =
        Point.some (geometricDifferenceX (k := k) V K) y h := by
  letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra
  have hxu := generic_x_ne_frobenius_x (k := k) V K
  have hb : (V⁄K).Nonsingular (XK k K) ((V⁄k).yCoord K) :=
    (((V⁄k)⁄K).equation_iff_nonsingular).mp (yCoord_equation (V⁄k) K)
  change ∃ y h, (Point.some _ _ hb : (V⁄K).Point) -
    pointFrobenius V K (Point.some _ _ hb) = Point.some (geometricDifferenceX (k := k) V K) y h
  rw [pointFrobenius_some,sub_eq_add_neg,Point.neg_some,Point.add_of_X_ne hxu]
  exact ⟨_,_,rfl⟩

end
end Astra01.EllipticFrobenius
#print axioms Astra01.EllipticFrobenius.geometricDifferenceX_infinity

#print axioms Astra01.EllipticFrobenius.geometricDifference_some
