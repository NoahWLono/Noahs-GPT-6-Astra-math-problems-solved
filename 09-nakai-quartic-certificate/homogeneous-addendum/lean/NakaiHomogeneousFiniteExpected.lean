import NakaiHomogeneousFinite

/-!
Expanded specification for the finite-gradient-quotient homogeneous class.
The actual finiteness hypothesis is explicit. No Hessian nonmembership premise
is assumed. The operator and unrestricted generated algebra are written out.
-/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NakaiHomogeneousFiniteExpected
variable {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
abbrev P := MvPolynomial ι k
abbrev A (f : P (k := k) (ι := ι)) := P (k := k) (ι := ι) ⧸ Ideal.span ({f} : Set (P (k := k) (ι := ι)))

def multiplication (f : P (k := k) (ι := ι)) (a : A f) : Module.End k (A f) where
  toFun x := a*x
  map_add' x y := mul_add a x y
  map_smul' r x := mul_smul_comm r a x

def bracket (f : P (k := k) (ι := ι)) (T : Module.End k (A f)) (a : A f) :=
  T * multiplication f a - multiplication f a * T

def hessian (f : P (k := k) (ι := ι)) : Matrix ι ι (P (k := k) (ι := ι)) :=
  fun i j => pderiv i (pderiv j f)

def polynomialOperator (f : P (k := k) (ι := ι)) (d : ℕ) (r : ι) (p : P (k := k) (ι := ι)) :=
  (∑ i, ∑ j,
    ((hessian f).adjugate i r * X j + X i * (hessian f).adjugate j r -
      X r * (hessian f).adjugate i j) * pderiv i (pderiv j p)) +
  (((Fintype.card ι : P (k := k) (ι := ι))-2) * ((d : P (k := k) (ι := ι))-1)) *
    (∑ i, (hessian f).adjugate i r * pderiv i p)

theorem expected_finite_gradient_full_operator_separation
    (f : P (k := k) (ι := ι)) (d : ℕ)
    (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (hn : 3 ≤ Fintype.card ι)
    [Module.Finite k (P (k := k) (ι := ι) ⧸
      Ideal.span (Set.range (fun i : ι => pderiv i f)))] (r : ι) :
    ∃ Q : Module.End k (A f),
      (∀ p : P (k := k) (ι := ι), Q (Ideal.Quotient.mk _ p) =
        Ideal.Quotient.mk _ (polynomialOperator f d r p)) ∧
      (∀ a b c : A f, bracket f (bracket f (bracket f Q a) b) c = 0) ∧
      Q ∉ Algebra.adjoin k
        (Set.range (multiplication f) ∪
          Set.range (fun D : Derivation k (A f) (A f) => D.toLinearMap)) := by
  letI : Module.Finite k (P (k := k) (ι := ι) ⧸ NakaiFramework.gradientIdeal f) :=
    inferInstanceAs (Module.Finite k (P (k := k) (ι := ι) ⧸
      Ideal.span (Set.range (fun i : ι => pderiv i f))))
  obtain ⟨Q, hQ, ho, hnot⟩ :=
    NakaiHomogeneous.finite_gradient_full_operator_separation f d hf hd hn r
  refine ⟨Q, ?_, ho, hnot⟩
  intro p
  exact (hQ p).trans
    (congrArg (Ideal.Quotient.mk (Ideal.span ({f} : Set (P (k := k) (ι := ι)))))
      (NakaiHomogeneous.QP_apply f d r p))

#print axioms expected_finite_gradient_full_operator_separation
end NakaiHomogeneousFiniteExpected
