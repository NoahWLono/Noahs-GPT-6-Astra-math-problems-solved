import EllipticTranslationLocal
import Mathlib.Data.Set.Finite.Lattice

/-! Actual auxiliary-point existence over algebraically closed constants.
The finite doubling-fiber argument includes characteristic two. -/
namespace Astra01.EllipticPoints
noncomputable section
open WeierstrassCurve.Affine
open Polynomial
open scoped Polynomial.Bivariate
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
local instance : DecidableEq k := Classical.decEq _

theorem exists_point_over_x (x : k) : ∃ y : k, W.Nonsingular x y := by
  let p := W.polynomial.map (Polynomial.evalRingHom x)
  have hp : p.natDegree = 2 := (W.monic_polynomial.natDegree_map _).trans W.natDegree_polynomial
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root p (by
    intro h
    have hh : p.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some h
    omega)
  refine ⟨y, W.equation_iff_nonsingular.mp ?_⟩
  change p.eval y = 0 at hy
  simpa [p, polynomial, Equation, Polynomial.evalEval, eval_map] using hy

def pointOverX (x : k) : W.Point :=
  Point.some x (exists_point_over_x W x).choose (exists_point_over_x W x).choose_spec

theorem pointOverX_injective : Function.Injective (pointOverX W) := by
  intro x y h
  exact (Point.some.inj h).1

instance point_infinite : Infinite W.Point := Infinite.of_injective (pointOverX W) (pointOverX_injective W)

def xOption : W.Point → Option k
  | .zero => none
  | .some x _ _ => some x

theorem finite_x_fiber (x : Option k) : (xOption W ⁻¹' {x}).Finite := by
  classical
  cases x with
  | none =>
    have hs : xOption W ⁻¹' {none} = {0} := by
      ext P
      cases P <;> simp [xOption] <;> rfl
    rw [hs]
    exact Set.finite_singleton _
  | some x =>
    let Q := pointOverX W x
    apply ((Set.finite_singleton (-Q)).insert Q).subset
    intro P hP
    cases P with
    | zero => simp [xOption] at hP
    | some a b h =>
      have ha : a = x := Option.some.inj hP
      subst a
      obtain hb | hb := W.Y_eq_of_X_eq h.1 (exists_point_over_x W x).choose_spec.1 rfl
      · left
        change Point.some x b h = Point.some x (exists_point_over_x W x).choose _
        subst b
        rfl
      · right
        change Point.some x b h = Point.some x (W.negY x (exists_point_over_x W x).choose) _
        subst b
        rfl

theorem two_torsion_polynomial_ne_zero : W.twoTorsionPolynomial.toPoly ≠ 0 := by
  intro h
  have h4 : (4 : k) = 0 := by simpa [WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly] using congrArg (fun p : k[X] => p.coeff 3) h
  have hb2 : W.b₂ = 0 := by simpa [WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly] using congrArg (fun p : k[X] => p.coeff 2) h
  have hb6 : W.b₆ = 0 := by simpa [WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly] using congrArg (fun p : k[X] => p.coeff 0) h
  have h2 : (2 : k) = 0 := (sq_eq_zero_iff).mp (by simpa only [show (2 : k)^2 = 4 by norm_num] using h4)
  have ha1 : W.a₁ = 0 := sq_eq_zero_iff.mp (by simpa [WeierstrassCurve.b₂, h4] using hb2)
  have ha3 : W.a₃ = 0 := sq_eq_zero_iff.mp (by simpa [WeierstrassCurve.b₆, h4] using hb6)
  exact W.polynomialY_ne_zero (by simp [polynomialY, h2, ha1, ha3])

theorem two_torsion_x_root {x y : k} (h : W.Nonsingular x y)
    (ht : (2 : ℕ) • (Point.some x y h) = 0) : W.twoTorsionPolynomial.toPoly.IsRoot x := by
  have hn : Point.some x y h = -(Point.some x y h) :=
    eq_neg_of_add_eq_zero_left (by simpa only [two_nsmul] using ht)
  have hy : y = W.negY x y := (Point.some.inj hn).2
  have hy0 : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    rw [negY] at hy
    linear_combination hy
  have he := W.equation_iff' x y |>.mp h.1
  simp only [Polynomial.IsRoot, WeierstrassCurve.twoTorsionPolynomial, Cubic.toPoly,
    eval_add, eval_mul, eval_pow, eval_C, eval_X, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination (2 * y + W.a₁ * x + W.a₃) * hy0 - 4 * he

theorem finite_two_torsion : {P : W.Point | (2 : ℕ) • P = 0}.Finite := by
  let s : Set (Option k) := insert none (some '' {x : k | W.twoTorsionPolynomial.toPoly.IsRoot x})
  have hs : s.Finite := ((Polynomial.finite_setOf_isRoot (two_torsion_polynomial_ne_zero W)).image some).insert none
  apply (hs.preimage' (fun x _ => finite_x_fiber W x)).subset
  intro P hP
  cases P with
  | zero => exact Set.mem_insert _ _
  | some x y h => exact Set.mem_insert_of_mem _ ⟨x, two_torsion_x_root W h hP, rfl⟩

theorem finite_doubling_fiber (P : W.Point) : {Q : W.Point | (2 : ℕ) • Q = P}.Finite := by
  by_cases h : ∃ Q : W.Point, (2 : ℕ) • Q = P
  · obtain ⟨Q, hQ⟩ := h
    apply (finite_two_torsion W).of_injOn (f := fun R => R - Q)
    · intro R hR
      change (2 : ℕ) • (R - Q) = 0
      rw [nsmul_sub, hR, hQ, sub_self]
    · intro R hR S hS he
      exact sub_left_injective he
  · have he : {Q : W.Point | (2 : ℕ) • Q = P} = ∅ := by
      ext Q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hQ => h ⟨Q, hQ⟩
    rw [he]
    exact Set.finite_empty

theorem exists_auxiliary (P R : W.Point) :
    ∃ Q : W.Point, Q ≠ 0 ∧ (2 : ℕ) • Q ≠ P ∧ (2 : ℕ) • Q ≠ R := by
  obtain ⟨Q, hQ⟩ := ((finite_doubling_fiber W P).union (finite_doubling_fiber W R)).insert 0 |>.exists_notMem
  refine ⟨Q, ?_⟩
  simpa only [Set.mem_insert_iff, Set.mem_union, Set.mem_setOf_eq, not_or] using hQ

end
end Astra01.EllipticPoints
#print axioms Astra01.EllipticPoints.exists_auxiliary
