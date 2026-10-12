import NakaiHomogeneousConditional
import NakaiHessianFinite

/-! Full operator separation for homogeneous hypersurfaces with finite gradient
quotient. The Hessian nonmembership hypothesis of the conditional theorem is
discharged by the explicit pure-power determinant argument. No novelty is claimed. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NakaiHomogeneous
open NakaiFramework
variable {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]

theorem finite_gradient_full_operator_separation
    (f : P (k := k) (ι := ι)) (d : ℕ)
    (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (hn : 3 ≤ Fintype.card ι)
    [Module.Finite k (P (k := k) (ι := ι) ⧸ gradientIdeal f)] (r : ι) :
    ∃ Q : Module.End k (P (k := k) (ι := ι) ⧸ Ideal.span ({f} : Set (P (k := k) (ι := ι)))),
      (∀ p, Q (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (QP f d r p)) ∧
      IsOrderLE2 Q ∧ Q ∉ generated := by
  exact conditional_full_operator_separation f d hf hd hn
    (hessian_not_mem_of_finite f d hf hd) r

#print axioms finite_gradient_full_operator_separation
end NakaiHomogeneous
