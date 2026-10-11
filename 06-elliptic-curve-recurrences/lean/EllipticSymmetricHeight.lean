import ValuationSymmetricSquare

/-! Exact height additivity for the actual symmetric-square x-coordinate map. -/
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

theorem exp_vectorDivisor (z : ι → K) (hz : z ≠ 0) (P : W.Point) :
    WithZero.exp (vectorDivisor W K z hz P) =
      Finset.univ.sup (fun i => placeValuation k K (placeOfPoint W K P) (z i)) := by
  classical
  obtain ⟨hb,⟨i,_,hi⟩⟩ := vectorDivisor_valuation W K z hz P
  apply le_antisymm
  · rw [← hi]
    exact Finset.le_sup (f := fun j => placeValuation k K (placeOfPoint W K P) (z j)) (Finset.mem_univ i)
  · exact Finset.sup_le fun j _ => hb j

variable (V : WeierstrassCurve.Affine K)

def pointDivisor (P : V.Point) : W.Point →₀ ℤ := vectorDivisor W K P.xRep P.xRep_ne_zero

def pointHeight (P : V.Point) : ℤ := vectorHeight W K P.xRep P.xRep_ne_zero

theorem sym2x_divisor (A B : V.Point) :
    vectorDivisor W K (A.sym2x B) (A.sym2x_ne_zero B) = pointDivisor W K V A + pointDivisor W K V B := by
  classical
  ext P
  apply WithZero.exp_injective
  simp only [Finsupp.add_apply, WithZero.exp_add, pointDivisor, exp_vectorDivisor]
  have h2 : (Finset.univ : Finset (Fin 2)) = {0,1} := by decide
  have h3 : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  cases A with
  | zero =>
    cases B <;> simp [WeierstrassCurve.Affine.Point.sym2x, WeierstrassCurve.Affine.Point.xRep, h2,h3]
  | some x y h =>
    cases B with
    | zero => simp [WeierstrassCurve.Affine.Point.sym2x, WeierstrassCurve.Affine.Point.xRep,h2,h3]
    | some u v j =>
      simpa [WeierstrassCurve.Affine.Point.sym2x, WeierstrassCurve.Affine.Point.xRep,h2,h3,max_assoc] using
        valuation_symmetric_square (placeValuation k K (placeOfPoint W K P)) x u

theorem sym2x_height (A B : V.Point) :
    vectorHeight W K (A.sym2x B) (A.sym2x_ne_zero B) = pointHeight W K V A + pointHeight W K V B := by
  classical
  unfold vectorHeight pointHeight
  rw [sym2x_divisor]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
end
end Astra01.EllipticHeight
#print axioms Astra01.EllipticHeight.sym2x_divisor
#print axioms Astra01.EllipticHeight.sym2x_height
