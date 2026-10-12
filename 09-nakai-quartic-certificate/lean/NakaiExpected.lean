import NakaiConcrete

/-!
An expanded specification fixture: the polynomial, faithful multiplication maps,
three commutators, and unrestricted generated algebra are stated independently
of the abbreviations in the implementation theorem.
-/

noncomputable section
open MvPolynomial
open scoped BigOperators

namespace NakaiExpected

abbrev P := MvPolynomial (Fin 4) ℚ

def F : P :=
  X 0 ^ 4 + X 1 ^ 4 + X 2 ^ 4 + X 3 ^ 4 +
  X 0 ^ 2 * X 1 ^ 2 + X 0 ^ 2 * X 2 ^ 2 + X 0 ^ 2 * X 3 ^ 2 +
  X 1 ^ 2 * X 2 ^ 2 + X 1 ^ 2 * X 3 ^ 2 + X 2 ^ 2 * X 3 ^ 2

abbrev A := P ⧸ Ideal.span ({F} : Set P)

def multiplication (a : A) : Module.End ℚ A where
  toFun x := a * x
  map_add' x y := mul_add a x y
  map_smul' r x := mul_smul_comm r a x

def bracket (T : Module.End ℚ A) (a : A) : Module.End ℚ A :=
  T * multiplication a - multiplication a * T

def hessian : Matrix (Fin 4) (Fin 4) P := fun i j => pderiv i (pderiv j F)

def polynomialOperator (p : P) : P :=
  (∑ i : Fin 4, ∑ j : Fin 4,
    (hessian.adjugate i 0 * X j + X i * hessian.adjugate j 0 -
      X 0 * hessian.adjugate i j) * pderiv i (pderiv j p)) +
  6 * (∑ i : Fin 4, hessian.adjugate i 0 * pderiv i p)

/-- This specification mentions the literal mixed quartic, its actual quotient,
the explicit operator, and all derivations with no word-length bound. -/
theorem expected_full_operator_separation :
    ∃ Q : Module.End ℚ A,
      (∀ p : P, Q (Ideal.Quotient.mk _ p) =
        Ideal.Quotient.mk _ (polynomialOperator p)) ∧
      (∀ a b c : A, bracket (bracket (bracket Q a) b) c = 0) ∧
      Q ∉ Algebra.adjoin ℚ
        (Set.range multiplication ∪
          Set.range (fun D : Derivation ℚ A A => D.toLinearMap)) := by
  obtain ⟨Q, hQ, ho, hn⟩ := NakaiQuartic.quartic_full_operator_separation
  refine ⟨Q, ?_, ho, hn⟩
  intro p
  exact (hQ p).trans
    (congrArg (Ideal.Quotient.mk (Ideal.span ({NakaiQuartic.F} : Set P)))
      (NakaiQuartic.QP_apply p))

#print axioms NakaiExpected.expected_full_operator_separation

end NakaiExpected
