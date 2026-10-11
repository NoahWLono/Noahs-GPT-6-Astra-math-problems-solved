import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.LinearCombination

/-! Actual affine fibers of a general Weierstrass equation, counted by completing
its y square. This does not replace the curve by an assumed normal form. -/
namespace Astra01.EllipticTwist
noncomputable section
open WeierstrassCurve.Affine
variable {F : Type*} [Field F]
variable (W : WeierstrassCurve.Affine F)

def squareDiscriminant (x : F) : F := 4*x^3 + W.b₂*x^2 + 2*W.b₄*x + W.b₆

theorem equation_iff_square (h2 : (2 : F) ≠ 0) (x y : F) :
    W.Equation x y ↔ (2*y+W.a₁*x+W.a₃)^2 = squareDiscriminant W x := by
  rw [W.equation_iff]
  unfold squareDiscriminant WeierstrassCurve.b₂ WeierstrassCurve.b₄ WeierstrassCurve.b₆
  constructor
  · intro h
    linear_combination 4*h
  · intro h
    have h4 : (4 : F) ≠ 0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
    apply mul_left_cancel₀ h4
    linear_combination h

def squareFiberEquiv (h2 : (2 : F) ≠ 0) (x : F) :
    {y : F // W.Equation x y} ≃ {z : F // z^2 = squareDiscriminant W x} where
  toFun y := ⟨2*y+W.a₁*x+W.a₃, (equation_iff_square W h2 x y).mp y.property⟩
  invFun z := ⟨(z-W.a₁*x-W.a₃)/2, by
    rw [equation_iff_square W h2]
    have h : 2*((z-W.a₁*x-W.a₃)/2)+W.a₁*x+W.a₃ = z := by field_simp; ring
    rw [h]
    exact z.property⟩
  left_inv y := by apply Subtype.ext; dsimp; field_simp; ring
  right_inv z := by apply Subtype.ext; dsimp; field_simp; ring

variable [Fintype F]
local instance : DecidableEq F := Classical.decEq _

theorem affine_fiber_count (hF : ringChar F ≠ 2) (x : F) :
    (Nat.card {y : F // W.Equation x y} : ℤ) = quadraticChar F (squareDiscriminant W x)+1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  rw [Nat.card_congr (squareFiberEquiv W h2 x)]
  have h := quadraticChar_card_sqrts hF (squareDiscriminant W x)
  rw [Set.toFinset_card,← Nat.card_eq_fintype_card] at h
  exact h

end
end Astra01.EllipticTwist
#print axioms Astra01.EllipticTwist.affine_fiber_count
