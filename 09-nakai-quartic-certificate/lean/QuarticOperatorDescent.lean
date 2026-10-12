import QuarticOperatorCoefficients
noncomputable section
namespace NakaiQuartic
open MvPolynomial
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- Product rule including both ordered off-diagonal terms. -/
theorem QP_product (u v : P) :
    QP (u * v) = u * QP v + v * QP u +
      2 * ∑ i : Fin 4, (∑ j : Fin 4, B i j * pderiv j u) * pderiv i v := by
  simp only [QP_apply, pderiv_mul, map_add, Fin.sum_univ_four]
  simp only [B_symmetric 1 0, B_symmetric 2 0, B_symmetric 3 0,
    B_symmetric 2 1, B_symmetric 3 1, B_symmetric 3 2]
  ring

/-- Exact descent identity, quantified over arbitrary test polynomials. -/
theorem QP_F_mul (p : P) :
    QP (F * p) = F * (QP p + 8 * ∑ i : Fin 4, a i * pderiv i p) := by
  rw [QP_product, QP_F_zero]
  change F * QP p + p * 0 +
    2 * (∑ i : Fin 4, (∑ j : Fin 4, B i j * G j) * pderiv i p) = _
  simp only [B_mul_G]
  simp only [Fin.sum_univ_four]
  ring

theorem QP_F_mul_mem (p : P) : QP (F * p) ∈ Ideal.span {F} := by
  rw [QP_F_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem euler_identity : (∑ i : Fin 4, x i * G i) = (4 : ℚ) • F := by
  simp only [G_formula, Fin.sum_univ_four, Algebra.smul_def, map_natCast, map_ofNat]
  unfold F S
  ring

theorem F_mem_J : F ∈ J := by
  apply Ideal.mem_span_range_iff_exists_fun.mpr
  refine ⟨fun i => (1/4 : ℚ) • x i, ?_⟩
  simp only [smul_mul_assoc, ← Finset.smul_sum, euler_identity, smul_smul]
  norm_num

#print axioms NakaiQuartic.QP_F_mul
#print axioms NakaiQuartic.F_mem_J
end NakaiQuartic
