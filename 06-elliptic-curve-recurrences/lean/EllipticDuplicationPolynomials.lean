import EllipticXProjectiveValue
import Mathlib.Tactic.ComputeDegree

/-! The reduced degree-four rational map governing x under doubling on a
nonsingular general Weierstrass model, in characteristic different from two. -/
namespace Astra01.EllipticDuplication
noncomputable section
open Polynomial WeierstrassCurve.Affine
open scoped Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]

def numerator : k[X] := X^4-C W.b₄*X^2-C (2*W.b₆)*X-C W.b₈
def denominator : k[X] := W.twoTorsionPolynomial.toPoly

theorem numerator_degree : (numerator W).natDegree = 4 := by
  unfold numerator
  compute_degree <;> norm_num

theorem four_ne_zero (h2 : (2:k) ≠ 0) : (4:k) ≠ 0 := by
  convert mul_ne_zero h2 h2 using 1 <;> norm_num

theorem denominator_degree (h2 : (2:k) ≠ 0) : (denominator W).natDegree = 3 :=
  Cubic.natDegree_of_a_ne_zero (four_ne_zero h2)

theorem denominator_separable (h2 : (2:k) ≠ 0) : (denominator W).Separable := by
  have hq : denominator W ≠ 0 := by
    intro h
    have hd := denominator_degree W h2
    simp [h] at hd
  apply (nodup_roots_iff_of_splits hq (IsAlgClosed.splits _)).mp
  have hd := W.twoTorsionPolynomial_discr_ne_zero_of_isElliptic
    (isUnit_iff_ne_zero.mpr h2)
  have hn := (Cubic.discr_ne_zero_iff_roots_nodup
    (φ := RingHom.id k) (P := W.twoTorsionPolynomial) (four_ne_zero h2)
    (by simpa only [Polynomial.map_id] using IsAlgClosed.splits W.twoTorsionPolynomial.toPoly)).mp hd
  simpa only [Cubic.map_roots, Polynomial.map_id, denominator] using hn

theorem derivative_identity (x : k) :
    ((denominator W).derivative.eval x)^2 =
      16*(numerator W).eval x + (4*W.b₂+32*x)*(denominator W).eval x := by
  simp only [numerator, denominator, WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly,
    derivative_add, derivative_mul, derivative_pow, derivative_C, derivative_X,
    eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X, eval_natCast, eval_zero, eval_one]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem pair_coprime (h2 : (2:k) ≠ 0) : IsCoprime (numerator W) (denominator W) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed k k (numerator W) (denominator W)).mpr
  intro x
  by_cases hq : aeval x (denominator W) = 0
  · left
    intro hp
    have hd := (denominator_separable W h2).aeval_derivative_ne_zero hq
    have he := derivative_identity W x
    change (numerator W).eval x = 0 at hp
    change (denominator W).eval x = 0 at hq
    change (denominator W).derivative.eval x ≠ 0 at hd
    rw [hp, hq] at he
    simp only [mul_zero, add_zero] at he
    exact (pow_ne_zero 2 hd) he
  · exact Or.inr hq
end
end Astra01.EllipticDuplication
#print axioms Astra01.EllipticDuplication.pair_coprime
