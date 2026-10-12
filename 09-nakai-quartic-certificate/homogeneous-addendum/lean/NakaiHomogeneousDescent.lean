import NakaiHomogeneousEuler

noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NakaiHomogeneous
open NakaiFramework
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
variable (f : P (k := k) (ι := ι))

lemma rank_trace_left (r : ι) :
    (∑ i, ∑ j, (U f i r * X j) * H f i j) = X r * h f := by
  calc
    _ = ∑ j, X j * ∑ i, U f i r * H f i j := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp [U_col_mul_H, mul_ite]

lemma rank_trace_right (r : ι) :
    (∑ i, ∑ j, (X i * U f j r) * H f i j) = X r * h f := by
  calc
    _ = ∑ i, X i * ∑ j, U f j r * H f j i := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [H_symmetric f i j]
      ring
    _ = _ := by simp [U_col_mul_H, mul_ite]

lemma adjugate_trace :
    (∑ i, ∑ j, U f i j * H f i j) = (Fintype.card ι : P (k := k) (ι := ι)) * h f := by
  calc
    _ = ∑ i, ∑ j, U f i j * H f j i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [H_symmetric f i j]
    _ = _ := by simp [U_mul_H, nsmul_eq_mul]

lemma B_trace (r : ι) :
    (∑ i, ∑ j, B f r i j * H f i j) =
      (2 - (Fintype.card ι : P (k := k) (ι := ι))) * X r * h f := by
  simp only [B, add_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [rank_trace_left, rank_trace_right]
  have hlast : (∑ i, ∑ j, X r * U f i j * H f i j) =
      X r * ((Fintype.card ι : P (k := k) (ι := ι)) * h f) := by
    rw [← adjugate_trace f]
    simp only [Finset.mul_sum, mul_assoc]
  rw [hlast]
  ring

theorem QP_f_zero [CharZero k] (d : ℕ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (r : ι) :
    QP f d r f = 0 := by
  rw [QP_apply]
  change (∑ i, ∑ j, B f r i j * H f i j) + correction d * (∑ i, U f i r * pderiv i f) = 0
  rw [B_trace, correction]
  simp only [mul_assoc]
  rw [degree_mul_Ucol_grad f d hf hd r]
  ring

lemma second_product (r : ι) (u v : P (k := k) (ι := ι)) :
    (∑ i, ∑ j, B f r i j * pderiv i (pderiv j (u*v))) =
      u * (∑ i, ∑ j, B f r i j * pderiv i (pderiv j v)) +
      v * (∑ i, ∑ j, B f r i j * pderiv i (pderiv j u)) +
      2 * (∑ i, ∑ j, B f r i j * pderiv j u * pderiv i v) := by
  have hs : (∑ i, ∑ j, B f r i j * pderiv i u * pderiv j v) =
      ∑ i, ∑ j, B f r i j * pderiv j u * pderiv i v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [B_symmetric f r j i]
  calc
    _ = ∑ i, ∑ j,
      (u * (B f r i j * pderiv i (pderiv j v)) +
       v * (B f r i j * pderiv i (pderiv j u)) +
       B f r i j * pderiv i u * pderiv j v +
       B f r i j * pderiv j u * pderiv i v) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [pderiv_mul, map_add]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hs]
      ring

lemma first_product (r : ι) (u v : P (k := k) (ι := ι)) :
    (∑ i, U f i r * pderiv i (u*v)) =
      u * (∑ i, U f i r * pderiv i v) + v * (∑ i, U f i r * pderiv i u) := by
  calc
    _ = ∑ i, (u * (U f i r * pderiv i v) + v * (U f i r * pderiv i u)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pderiv_mul]
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem QP_product (d : ℕ) (r : ι) (u v : P (k := k) (ι := ι)) :
    QP f d r (u*v) = u * QP f d r v + v * QP f d r u +
      2 * ∑ i, (∑ j, B f r i j * pderiv j u) * pderiv i v := by
  simp only [QP_apply, second_product, first_product, Finset.sum_mul]
  ring

/-- Exact descent, with every polynomial multiplier quantified. -/
theorem QP_f_mul [CharZero k] (d : ℕ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (r : ι) (p : P (k := k) (ι := ι)) :
    QP f d r (f*p) = f * (QP f d r p +
      (2*(d : P (k := k) (ι := ι))) * ∑ i, U f i r * pderiv i p) := by
  rw [QP_product, QP_f_zero f d hf hd r]
  simp only [B_mul_grad f d hf hd, mul_zero, add_zero]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

theorem QP_f_mul_mem [CharZero k] (d : ℕ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (r : ι) (p : P (k := k) (ι := ι)) :
    QP f d r (f*p) ∈ Ideal.span ({f} : Set (P (k := k) (ι := ι))) := by
  rw [QP_f_mul f d hf hd]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton f))

#print axioms QP_f_zero
#print axioms QP_product
#print axioms QP_f_mul
end NakaiHomogeneous
