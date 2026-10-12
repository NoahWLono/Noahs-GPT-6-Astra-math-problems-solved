import NakaiFramework
import NakaiJacobi

/-!
Explicit ordinary-homogeneous cofactor operator in arbitrary finite dimension.
These are algebraic definitions and identities, not a socle nonmembership theorem.
-/
noncomputable section
open MvPolynomial
open scoped BigOperators

namespace NakaiHomogeneous
open NakaiFramework
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev P := MvPolynomial ι k

def H (f : P (k := k) (ι := ι)) : Matrix ι ι (P (k := k) (ι := ι)) :=
  fun i j => pderiv i (pderiv j f)
def U (f : P (k := k) (ι := ι)) := (H f).adjugate
def h (f : P (k := k) (ι := ι)) := (H f).det

def B (f : P (k := k) (ι := ι)) (r : ι) (i j : ι) : P (k := k) (ι := ι) :=
  U f i r * X j + X i * U f j r - X r * U f i j

def correction (d : ℕ) : P (k := k) (ι := ι) :=
  ((Fintype.card ι : P (k := k) (ι := ι)) - 2) * ((d : P (k := k) (ι := ι)) - 1)

def QP (f : P (k := k) (ι := ι)) (d : ℕ) (r : ι) :
    Module.End k (P (k := k) (ι := ι)) :=
  (∑ i, ∑ j, mulEnd (B f r i j) * (pderiv i).toLinearMap * (pderiv j).toLinearMap) +
  ∑ i, mulEnd (correction d * U f i r) * (pderiv i).toLinearMap

@[simp] theorem QP_apply (f : P (k := k) (ι := ι)) (d : ℕ) (r : ι) (p : P (k := k) (ι := ι)) :
    QP f d r p = (∑ i, ∑ j, B f r i j * pderiv i (pderiv j p)) +
      correction d * ∑ i, U f i r * pderiv i p := by
  simp only [QP, LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply,
    mulEnd_apply, Derivation.coeFn_coe, Finset.mul_sum, mul_assoc]

theorem QP_orderLE2 (f : P (k := k) (ι := ι)) (d : ℕ) (r : ι) :
    IsOrderLE2 (QP f d r) :=
  orderLE2_secondOrder (B f r) (fun i => correction d * U f i r) (fun i => pderiv i)

theorem H_symmetric (f : P (k := k) (ι := ι)) (i j : ι) : H f i j = H f j i :=
  pderiv_comm i j f

theorem U_symmetric (f : P (k := k) (ι := ι)) (i j : ι) : U f i j = U f j i := by
  have hs : (H f).IsSymm := Matrix.IsSymm.ext (fun i j => H_symmetric f j i)
  exact hs.adjugate.apply j i

theorem B_symmetric (f : P (k := k) (ι := ι)) (r i j : ι) :
    B f r i j = B f r j i := by
  simp only [B, U_symmetric f j i]
  ring

/-- One row of the adjugate-Hessian identity. -/
theorem U_mul_H (f : P (k := k) (ι := ι)) (i j : ι) :
    (∑ l, U f i l * H f l j) = if i = j then h f else 0 := by
  have heq := congrArg (fun M : Matrix ι ι (P (k := k) (ι := ι)) => M i j)
    (Matrix.adjugate_mul (H f))
  simpa [U, h, Matrix.mul_apply, Matrix.one_apply] using heq

theorem U_col_mul_H (f : P (k := k) (ι := ι)) (r j : ι) :
    (∑ i, U f i r * H f i j) = if r = j then h f else 0 := by
  simp_rw [U_symmetric f _ r]
  exact U_mul_H f r j

/-- Jacobi's determinant derivative, specialized to the actual Hessian. -/
theorem pderiv_h (f : P (k := k) (ι := ι)) (j : ι) :
    pderiv j (h f) = ∑ i, ∑ l, U f i l * pderiv j (H f i l) := by
  rw [h, NakaiJacobi.derivation_det]
  change (∑ i, ∑ l, U f l i * pderiv j (H f i l)) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  rw [U_symmetric f l i]

#print axioms QP_orderLE2
#print axioms U_mul_H
#print axioms pderiv_h
end NakaiHomogeneous
