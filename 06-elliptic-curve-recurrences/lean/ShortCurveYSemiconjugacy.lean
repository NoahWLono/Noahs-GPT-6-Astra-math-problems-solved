import EllipticXYDegrees

/-! The actual y-coordinate semiconjugacy on y²=x³+1. This algebraic identity
is valid wherever this short model is nonsingular, not only in characteristic 7. -/
namespace Astra01
noncomputable section

section Identity
variable {L : Type*} [Field L]
theorem short_y_translation_identity (x y : L) (hx : x ≠ 0) (he : y^2 = x^3 + 1) :
    -(((y-1)/x) * (((y-1)/x)^2 - x - x) + y) = (y-3)/(y+1) := by
  have hy : y + 1 ≠ 0 := by
    intro h
    have hy1 : y = -1 := eq_neg_of_add_eq_zero_left h
    have hx3 : x^3 = 0 := by rw [hy1] at he; linear_combination -he
    exact (pow_ne_zero 3 hx) hx3
  field_simp [hx, hy]
  linear_combination -(y-1)^2 * he
end Identity

namespace EllipticPointDivisor
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open EllipticTranslation
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
  (ha4 : W.a₄ = 0) (ha6 : W.a₆ = 1)
local instance : DecidableEq k := Classical.decEq _

include ha1 ha2 ha3 ha4 ha6

theorem short_unit_point_nonsingular : W.Nonsingular 0 1 := by
  apply W.equation_iff_nonsingular.mp
  simp [W.equation_iff, ha1, ha2, ha3, ha4, ha6]

def shortUnitPoint : W.Point := Point.some 0 1 (short_unit_point_nonsingular W ha1 ha2 ha3 ha4 ha6)

theorem short_unit_point_double (h2 : (2 : k) ≠ 0) :
    shortUnitPoint W ha1 ha2 ha3 ha4 ha6 + shortUnitPoint W ha1 ha2 ha3 ha4 ha6 =
      -shortUnitPoint W ha1 ha2 ha3 ha4 ha6 := by
  have hy : (1 : k) ≠ W.negY 0 1 := by
    simp only [negY, ha1, ha3, zero_mul, sub_zero]
    intro h
    apply h2
    linear_combination h
  unfold shortUnitPoint
  rw [Point.add_self_of_Y_ne hy, Point.neg_some]
  congr 1 <;> simp [slope, addX, addY, negAddY, negY, ha1, ha2, ha3, ha4]

theorem short_unit_point_order (h2 : (2 : k) ≠ 0) :
    addOrderOf (shortUnitPoint W ha1 ha2 ha3 ha4 ha6) = 3 := by
  let G := shortUnitPoint W ha1 ha2 ha3 ha4 ha6
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply addOrderOf_eq_prime
  · have hd : G + G = -G := short_unit_point_double W ha1 ha2 ha3 ha4 ha6 h2
    change 3 • G = 0
    rw [show (3 : ℕ) = 2+1 from rfl, add_nsmul, two_nsmul, one_nsmul, hd, neg_add_cancel]
  · exact Point.some_ne_zero _

variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : DecidableEq K := Classical.decEq _

/-- Actual global equality in the elliptic function field. -/
theorem short_y_semiconjugacy :
    translationEquiv W K (shortUnitPoint W ha1 ha2 ha3 ha4 ha6) (W.yCoord K) =
      (W.yCoord K - 3) / (W.yCoord K + 1) := by
  have ht := (translation_coordinates W K (short_unit_point_nonsingular W ha1 ha2 ha3 ha4 ha6)).2
  have hx : XK k K ≠ 0 := xCoord_ne_zero W K
  have he : W.yCoord K ^ 2 = XK k K ^ 3 + 1 := by
    have h := (W⁄K).equation_iff _ _ |>.mp (yCoord_equation W K)
    simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map, ha1, ha2, ha3, ha4, ha6] using h
  have hid := short_y_translation_identity (XK k K) (W.yCoord K) hx he
  simp [slope, addX, addY, negAddY, negY, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, ha1, ha2, ha3, ha4, hx] at ht
  exact ht.trans (by simpa only [neg_add_rev] using hid)

end EllipticPointDivisor
end
end Astra01
#print axioms Astra01.EllipticPointDivisor.short_unit_point_order
#print axioms Astra01.EllipticPointDivisor.short_y_semiconjugacy
