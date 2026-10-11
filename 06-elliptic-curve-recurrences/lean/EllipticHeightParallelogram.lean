import EllipticSymmetricHeight

/-! The exact parallelogram law for actual elliptic points over the source
function field, with constant coefficients. -/
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

theorem pointHeight_parallelogram (V : WeierstrassCurve.Affine k) [V.IsElliptic]
    (A B : (V.map (algebraMap k K)).Point) :
    pointHeight W K _ (A+B) + pointHeight W K _ (A-B) =
      2 * pointHeight W K _ A + 2 * pointHeight W K _ B := by
  classical
  let V' := V.map (algebraMap k K)
  let z := A.sym2x B
  let t := (A+B).sym2x (A-B)
  have hz : z ≠ 0 := A.sym2x_ne_zero B
  have ht : t ≠ 0 := (A+B).sym2x_ne_zero (A-B)
  have hm : vectorHeight W K (EllipticAddSub.mapVector V' z) (V'.addSubMap_ne_zero hz) =
      vectorHeight W K z hz + vectorHeight W K z hz := by
    unfold vectorHeight
    rw [vectorDivisor_addSubMap, two_nsmul]
    exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  obtain ⟨c,hc,he⟩ := EllipticAddSub.mapVector_add_sub V' A B
  have hs : vectorHeight W K (EllipticAddSub.mapVector V' z) (V'.addSubMap_ne_zero hz) =
      vectorHeight W K t ht := by
    simpa only [z,t,he] using vectorHeight_smul W K t ht c hc
  have h := hs.symm.trans hm
  dsimp only [z,t] at h
  rw [sym2x_height, sym2x_height] at h
  linear_combination h
end
end Astra01.EllipticHeight
#print axioms Astra01.EllipticHeight.pointHeight_parallelogram
