import EllipticAddSubAlgebra

/-! A cancellation-free chord numerator for the infinity calculation in the
finite-field Frobenius difference. All coefficients and curve equations are actual. -/
namespace Astra01.EllipticAddSub
noncomputable section
open WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k)

theorem chordNumerator_expansion {x u y v : k}
    (hy : W.Equation x y) (hv : W.Equation u v) :
    chordNumerator W x u y v =
      x*u^2 + x^2*u + 2*W.a₂*x*u + W.a₄*(x+u) + 2*W.a₆ -
        2*y*v - W.a₁*(x*v+u*y) - W.a₃*(y+v) := by
  have h1 := (W.equation_iff x y).mp hy
  have h2 := (W.equation_iff u v).mp hv
  unfold chordNumerator
  linear_combination h1 + h2

end
end Astra01.EllipticAddSub
#print axioms Astra01.EllipticAddSub.chordNumerator_expansion
