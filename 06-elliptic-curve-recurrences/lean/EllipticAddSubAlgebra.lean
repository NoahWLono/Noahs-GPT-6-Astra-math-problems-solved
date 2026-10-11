import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination

/-! Denominator-cleared symmetric addition/subtraction identities. -/
namespace Astra01.EllipticAddSub
noncomputable section
open WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k)

def chordNumerator (x u y v : k) : k :=
  (v-y)^2 + W.a₁*(v-y)*(u-x) - (W.a₂+x+u)*(u-x)^2

theorem chordNumerator_sum {x u y v : k} (hy : W.Equation x y) (hv : W.Equation u v) :
    chordNumerator W x u y v + chordNumerator W x u y (W.negY u v) =
      2*(x+u)*(x*u) + W.b₂*(x*u) + W.b₄*(x+u) + W.b₆ := by
  have h1 := (W.equation_iff x y).mp hy
  have h2 := (W.equation_iff u v).mp hv
  unfold chordNumerator negY
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination 2*h1 + 2*h2

theorem chordNumerator_product {x u y v : k} (hy : W.Equation x y) (hv : W.Equation u v) :
    chordNumerator W x u y v * chordNumerator W x u y (W.negY u v) =
      (u-x)^2*((x*u)^2-W.b₄*(x*u)-W.b₆*(x+u)-W.b₈) := by
  have h1 := (W.equation_iff x y).mp hy
  have h2 := (W.equation_iff u v).mp hv
  unfold chordNumerator negY
  simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination (-W.a₁^2*u^2 + W.a₁^2*u*x - W.a₁*W.a₃*u + W.a₁*W.a₃*x - 2*W.a₁*u*v + W.a₁*x*y - 2*W.a₂*u^2 + 4*W.a₂*u*x - W.a₂*x^2 - 2*W.a₃*v + W.a₃*y + W.a₄*x + W.a₆ - 2*u^3 + 2*u^2*x + 2*u*x^2 - 2*v^2 - x^3 + y^2)*h1 +
    (W.a₁^2*u*x - W.a₁^2*x^2 + W.a₁*W.a₃*u - W.a₁*W.a₃*x + W.a₁*u*v - W.a₂*u^2 + 4*W.a₂*u*x - 4*W.a₂*x^2 + W.a₃*v + W.a₄*u - 2*W.a₄*x - W.a₆ - u^3 + 2*u^2*x + 2*u*x^2 + v^2 - 4*x^3)*h2
end
end Astra01.EllipticAddSub
#print axioms Astra01.EllipticAddSub.chordNumerator_sum
#print axioms Astra01.EllipticAddSub.chordNumerator_product
