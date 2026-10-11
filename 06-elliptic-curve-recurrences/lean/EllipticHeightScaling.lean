import EllipticProjectiveHeightDivisor
import EllipticAddSubMaxValuation

/-! Projective scalar invariance and exact quadratic height-divisor scaling. -/
namespace Astra01.EllipticHeight
noncomputable section
open WeierstrassCurve.Affine.Chart FunctionField.Chart
open Astra01.EllipticPointDivisor
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq K := Classical.decEq _

theorem vectorDivisor_eq_of_bounds (z : ι → K) (hz : z ≠ 0) (P : W.Point) (a : ℤ)
    (hb : ∀ i, placeValuation k K (placeOfPoint W K P) (z i) ≤ WithZero.exp a)
    (he : ∃ i, placeValuation k K (placeOfPoint W K P) (z i) = WithZero.exp a) :
    vectorDivisor W K z hz P = a := by
  obtain ⟨hs,⟨i,_,hi⟩⟩ := vectorDivisor_valuation W K z hz P
  obtain ⟨j,hj⟩ := he
  apply le_antisymm
  · exact WithZero.exp_le_exp.mp (hi ▸ hb i)
  · exact WithZero.exp_le_exp.mp (hj ▸ hs j)

theorem vectorDivisor_smul (z : ι → K) (hz : z ≠ 0) (c : K) (hc : c ≠ 0) :
    vectorDivisor W K (c • z) (smul_ne_zero hc hz) = vectorDivisor W K z hz -
      principalDivisor W K (Additive.ofMul (Units.mk0 c hc)) := by
  ext P
  change vectorDivisor W K (c • z) _ P = vectorDivisor W K z hz P -
    principalDivisor W K (Additive.ofMul (Units.mk0 c hc)) P
  have hv := point_valuation_unit W K (Units.mk0 c hc) P
  change placeValuation k K (placeOfPoint W K P) c = _ at hv
  obtain ⟨hb,⟨i,_,hi⟩⟩ := vectorDivisor_valuation W K z hz P
  have hp : placeValuation k K (placeOfPoint W K P) c *
      WithZero.exp (vectorDivisor W K z hz P) =
      WithZero.exp (vectorDivisor W K z hz P -
        principalDivisor W K (Additive.ofMul (Units.mk0 c hc)) P) := by
    rw [hv, ← WithZero.exp_add]
    congr 1
    ring
  apply vectorDivisor_eq_of_bounds
  · intro j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← hp]
    exact mul_le_mul_left' (hb j) _
  · refine ⟨i,?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [hi,hp]

def vectorHeight (z : ι → K) (hz : z ≠ 0) : ℤ := (vectorDivisor W K z hz).sum (fun _ n => n)

theorem vectorHeight_smul (z : ι → K) (hz : z ≠ 0) (c : K) (hc : c ≠ 0) :
    vectorHeight W K (c • z) (smul_ne_zero hc hz) = vectorHeight W K z hz := by
  unfold vectorHeight
  rw [vectorDivisor_smul W K z hz c hc, Finsupp.sum_sub_index (fun _ _ _ => rfl),
    sum_principalDivisor_eq_zero, sub_zero]

theorem vectorDivisor_addSubMap (V : WeierstrassCurve.Affine k) [V.IsElliptic]
    (z : Fin 3 → K) (hz : z ≠ 0) :
    vectorDivisor W K (EllipticAddSub.mapVector (V.map (algebraMap k K)) z)
      ((V.map (algebraMap k K)).addSubMap_ne_zero hz) = (2 : ℕ) • vectorDivisor W K z hz := by
  ext P
  change vectorDivisor W K _ _ P = (2 : ℕ) • vectorDivisor W K z hz P
  obtain ⟨hb,⟨i,hi,he⟩⟩ := vectorDivisor_valuation W K z hz P
  have hm := EllipticAddSub.mapVector_maximum V (algebraMap k K)
    (placeValuation k K (placeOfPoint W K P))
    (placeValuation_algebraMap_le_one k K (placeOfPoint W K P)) z (z i) hi
    (fun j => by rw [he]; exact hb j) ⟨i,rfl⟩
  apply vectorDivisor_eq_of_bounds
  · simpa only [he, ← WithZero.exp_nsmul] using hm.1
  · simpa only [he, ← WithZero.exp_nsmul] using hm.2
end
end Astra01.EllipticHeight
#print axioms Astra01.EllipticHeight.vectorHeight_smul
#print axioms Astra01.EllipticHeight.vectorDivisor_addSubMap
