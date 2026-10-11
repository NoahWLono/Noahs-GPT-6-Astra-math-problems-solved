import EllipticFrobeniusRationalPoles
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets

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

local instance : (V⁄F).IsElliptic := inferInstanceAs (V.map (algebraMap F F)).IsElliptic

theorem rational_count_le_difference_pole_degree :
    2 * Nat.card (V⁄F).Point ≤
      divisorDegree (V⁄k) (poleDivisor (V⁄k) K (geometricDifferenceUnit (k := k) V K)) := by
  classical
  letI : Fintype (WithZero {xy : F × F // (V⁄F).Equation xy.1 xy.2}) :=
    inferInstanceAs (Fintype (Option {xy : F × F // (V⁄F).Equation xy.1 xy.2}))
  letI : Fintype (V⁄F).Point := Fintype.ofInjective (V⁄F).pointEquiv (V⁄F).pointEquiv.injective
  let e : (V⁄F).Point ↪ (V⁄k).Point :=
    ⟨Point.baseChange F k, Point.map_injective (Algebra.ofId F k)⟩
  let D := poleDivisor (V⁄k) K (geometricDifferenceUnit (k := k) V K)
  have hs : Finset.univ.map e ⊆ D.support := by
    intro P hP
    obtain ⟨T,_,rfl⟩ := Finset.mem_map.mp hP
    apply Finsupp.mem_support_iff.mpr
    change poleDivisor (V⁄k) K (geometricDifferenceUnit (k := k) V K) (Point.baseChange F k T) ≠ 0
    rw [geometricDifference_pole_rational]
    decide
  calc
    2 * Nat.card (V⁄F).Point = ∑ T : (V⁄F).Point, D (e T) := by
      simp [D,e,geometricDifference_pole_rational,Nat.card_eq_fintype_card,mul_comm]
    _ = ∑ P ∈ Finset.univ.map e, D P := by rw [Finset.sum_map]
    _ ≤ divisorDegree (V⁄k) D := Finset.sum_le_sum_of_subset hs

theorem rational_count_le_difference_height :
    letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra;
    2 * (Nat.card (V⁄F).Point : ℤ) ≤
      pointHeight (V⁄k) K (V⁄K)
        (geometricGeneric V K - pointFrobenius V K (geometricGeneric V K)) := by
  letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra
  obtain ⟨y,hy,hpoint⟩ := geometricDifference_some (k := k) V K
  rw [hpoint,pointHeight_some (V⁄k) K (V⁄K) hy (geometricDifferenceX_ne_zero (k := k) V K)]
  exact_mod_cast rational_count_le_difference_pole_degree (k := k) V K

end
end Astra01.EllipticFrobenius
#print axioms Astra01.EllipticFrobenius.rational_count_le_difference_pole_degree
#print axioms Astra01.EllipticFrobenius.rational_count_le_difference_height
