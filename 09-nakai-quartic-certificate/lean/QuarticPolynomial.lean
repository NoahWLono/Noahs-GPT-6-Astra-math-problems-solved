import QuarticOperatorDescent
noncomputable section
namespace NakaiQuartic
open MvPolynomial
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- The coefficient 8 is the n=d=4 Jacobian escape factor. -/
theorem QP_G0_identity : QP (G 0) =
    8 * h - 3 * ∑ i : Fin 4, pderiv 0 (a i) * G i := by
  rw [QP_apply, h_cofactor]
  simp only [Fin.sum_univ_four, B, a, C_factored, G_formula]
  norm_num [C₀, D, H₀, S, Fin.succAbove, Fin.ext_iff, pderiv_mul, pderiv_pow]
  ring

set_option maxRecDepth 4096 in
theorem separator_QP_G0 : separator (QP (G 0)) = -622080 := by
  rw [QP_G0_identity]
  have hn (n : ℕ) (p : P) : separator (n * p) = n * separator p := by
    simpa only [nsmul_eq_mul] using (map_nsmul separator n p)
  have h8 : separator (8 * h) = 8 * separator h := by
    simpa only [Nat.cast_ofNat] using hn 8 h
  have h3 : separator (3 * ∑ i : Fin 4, pderiv 0 (a i) * G i) =
      3 * separator (∑ i : Fin 4, pderiv 0 (a i) * G i) := by
    simpa only [Nat.cast_ofNat] using hn 3 (∑ i : Fin 4, pderiv 0 (a i) * G i)
  rw [map_sub, h8, h3, separator_h, map_sum]
  have hz : (∑ i : Fin 4, separator (pderiv 0 (a i) * G i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simpa only [mul_comm] using separator_G_mul i (pderiv 0 (a i))
  rw [hz]
  norm_num

theorem QP_G0_not_mem_J : QP (G 0) ∉ J := by
  intro hp
  have hz := separator_zero_of_mem_J hp
  rw [separator_QP_G0] at hz
  norm_num at hz

#print axioms NakaiQuartic.separator_G_mul
#print axioms NakaiQuartic.separator_h
#print axioms NakaiQuartic.QP_F_mul
#print axioms NakaiQuartic.QP_G0_not_mem_J

end NakaiQuartic
