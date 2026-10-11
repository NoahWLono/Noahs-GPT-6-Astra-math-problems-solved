import EllipticDuplicationPolynomials

/-! The reduced duplication rational map agrees at every point with actual
elliptic doubling, including the identity and all two-torsion points. -/
namespace Astra01.EllipticDuplication
noncomputable section
open Polynomial WeierstrassCurve.Affine
open Astra01.EllipticPointDivisor
open scoped Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
local instance : DecidableEq k := Classical.decEq _

theorem denominator_square {x y : k} (h : W.Equation x y) :
    (denominator W).eval x = (y-W.negY x y)^2 := by
  have he := (W.equation_iff x y).mp h
  simp only [denominator, WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly,
    eval_add, eval_mul, eval_pow, eval_C, eval_X, negY,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination -4*he

theorem numerator_doubling_identity {x y : k} (h : W.Equation x y) :
    (3*x^2+2*W.a₂*x+W.a₄-W.a₁*y)^2 +
      W.a₁*(3*x^2+2*W.a₂*x+W.a₄-W.a₁*y)*(y-W.negY x y) -
      (W.a₂+2*x)*(y-W.negY x y)^2 = (numerator W).eval x := by
  have he := (W.equation_iff x y).mp h
  simp only [numerator, eval_sub, eval_mul, eval_pow, eval_C, eval_X, negY,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination -(W.a₁^2+4*W.a₂+8*x)*he

theorem doubling_x_formula {x y : k} (h : W.Equation x y) (hy : y ≠ W.negY x y) :
    W.addX x x (W.slope x x y y) = (numerator W).eval x / (denominator W).eval x := by
  rw [W.slope_of_Y_ne rfl hy, denominator_square W h]
  have hd : y-W.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have he := numerator_doubling_identity W h
  unfold addX
  field_simp [hd]
  linear_combination he

theorem projective_doubling (h2 : (2:k) ≠ 0) (P : W.Point) :
    coordinateXValue W (P+P) =
      rationalProjectiveMap (numerator W) (denominator W) (coordinateXValue W P) := by
  cases P with
  | zero =>
    change coordinateXValue W (0+0) = _
    rw [add_zero]
    simp [coordinateXValue, rationalProjectiveMap, numerator_degree W, denominator_degree W h2]
  | some x y h =>
    by_cases hy : y = W.negY x y
    · rw [Point.add_self_of_Y_eq hy]
      change none = rationalProjectiveMap (numerator W) (denominator W) (some x)
      have hq : (denominator W).eval x = 0 := by rw [denominator_square W h.1, sub_eq_zero.mpr hy, zero_pow (by decide)]
      simp [rationalProjectiveMap, hq]
    · rw [Point.add_self_of_Y_ne hy]
      change some (W.addX x x (W.slope x x y y)) =
        rationalProjectiveMap (numerator W) (denominator W) (some x)
      have hq : (denominator W).eval x ≠ 0 := by
        rw [denominator_square W h.1]
        exact pow_ne_zero 2 (sub_ne_zero.mpr hy)
      simp only [rationalProjectiveMap, hq, ↓reduceIte, Option.some.injEq]
      exact doubling_x_formula W h.1 hy
end
end Astra01.EllipticDuplication
#print axioms Astra01.EllipticDuplication.projective_doubling
