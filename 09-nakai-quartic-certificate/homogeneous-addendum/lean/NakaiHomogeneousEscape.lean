import NakaiHomogeneousDescent

/-! Exact polynomial escape identity; Hessian nonmembership is not assumed here. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NakaiHomogeneous
open NakaiFramework
variable {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
variable (f : P (k := k) (ι := ι)) (d : ℕ)

omit [CharZero k] [DecidableEq ι] in
theorem euler_H (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (i j : ι) :
    (∑ l, X l * pderiv l (H f i j)) =
      ((d : P (k := k) (ι := ι)) - 2) * H f i j := by
  have hh : (H f i j).IsHomogeneous (d-2) := by
    simpa only [H, Nat.sub_sub, one_add_one_eq_two] using
      ((hf.pderiv (i := j)).pderiv (i := i))
  simpa only [nsmul_eq_mul, Nat.cast_sub hd, Nat.cast_ofNat] using hh.sum_X_mul_pderiv

lemma grad_rank_left (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (r : ι) :
    (∑ i, ∑ j, (U f i r * X j) * pderiv i (pderiv j (pderiv r f))) =
      ((d : P (k := k) (ι := ι)) - 2) * h f := by
  calc
    _ = ∑ i, U f i r * ∑ j, X j * pderiv j (H f i r) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [H, pderiv_comm i j (pderiv r f)]
      ring
    _ = ∑ i, U f i r * (((d : P (k := k) (ι := ι)) - 2) * H f i r) := by
      simp_rw [euler_H f d hf hd]
    _ = ((d : P (k := k) (ι := ι)) - 2) * ∑ i, U f i r * H f i r := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [U_col_mul_H]; simp

lemma grad_rank_right (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (r : ι) :
    (∑ i, ∑ j, (X i * U f j r) * pderiv i (pderiv j (pderiv r f))) =
      ((d : P (k := k) (ι := ι)) - 2) * h f := by
  rw [← grad_rank_left f d hf hd r, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pderiv_comm j i (pderiv r f)]
  ring

omit [CharZero k] in
lemma grad_adjugate_term (r : ι) :
    (∑ i, ∑ j, (X r * U f i j) * pderiv i (pderiv j (pderiv r f))) =
      X r * pderiv r (h f) := by
  rw [pderiv_h]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [H, pderiv_comm j r f, pderiv_comm i r (pderiv j f)]
  ring

lemma QP_gradient_preliminary (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (r : ι) :
    QP f d r (pderiv r f) =
      (2*((d : P (k := k) (ι := ι))-2) + correction d) * h f - X r * pderiv r (h f) := by
  rw [QP_apply]
  change (∑ i, ∑ j, B f r i j * pderiv i (pderiv j (pderiv r f))) +
    correction d * (∑ i, U f i r * H f i r) = _
  simp only [B, add_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [grad_rank_left f d hf hd r, grad_rank_right f d hf hd r, grad_adjugate_term,
    U_col_mul_H]
  simp only [ite_true]
  ring

lemma X_pderiv_h (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (r : ι) :
    X r * pderiv r (h f) = ((d : P (k := k) (ι := ι))-2) * h f +
      ((d : P (k := k) (ι := ι))-1) * ∑ i, pderiv r (U f i r) * pderiv i f := by
  have he := congrArg (fun p : P (k := k) (ι := ι) => pderiv r p)
    (degree_mul_Ucol_grad f d hf hd r)
  simp only [pderiv_mul, map_sub, Derivation.map_natCast, pderiv_one, sub_zero,
    zero_mul, zero_add, map_sum, pderiv_X, Pi.single_eq_same, mul_one] at he
  have hs : (∑ i, (pderiv r (U f i r) * pderiv i f +
      U f i r * pderiv r (pderiv i f))) =
      h f + ∑ i, pderiv r (U f i r) * pderiv i f := by
    rw [Finset.sum_add_distrib]
    have hsecond : (∑ i, U f i r * pderiv r (pderiv i f)) = h f := by
      change (∑ i, U f i r * H f r i) = _
      simp_rw [H_symmetric f r]
      rw [U_col_mul_H]
      simp
    rw [hsecond]
    ring
  rw [hs] at he
  calc
    _ = ((d : P (k := k) (ι := ι))-1) *
        (h f + ∑ i, pderiv r (U f i r) * pderiv i f) - h f := by
      calc
        _ = (pderiv r (h f) * X r + h f) - h f := by ring
        _ = _ := by rw [← he]
    _ = _ := by ring

/-- The exact gradient-generator identity used by the conditional separator. -/
theorem QP_gradient (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (r : ι) :
    QP f d r (pderiv r f) =
      ((Fintype.card ι : P (k := k) (ι := ι)) * d - Fintype.card ι - d) * h f -
      ((d : P (k := k) (ι := ι))-1) * ∑ i, pderiv r (U f i r) * pderiv i f := by
  rw [QP_gradient_preliminary f d hf hd r, X_pderiv_h f d hf hd r, correction]
  ring

#print axioms QP_gradient
end NakaiHomogeneous
