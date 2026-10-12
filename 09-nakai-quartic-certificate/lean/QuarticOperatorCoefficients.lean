import QuarticSeparator
noncomputable section
namespace NakaiQuartic
open MvPolynomial
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- Symmetry is checked for the actual adjugate coefficients. -/
theorem B_symmetric (i j : Fin 4) : B i j = B j i := by
  fin_cases i <;> fin_cases j <;>
    simp only [B, a, C_factored] <;>
    norm_num [C₀] <;> ring

/-- The cancellation which makes descent work on every multiple of F. -/
theorem B_mul_G (i : Fin 4) :
    (∑ j : Fin 4, B i j * G j) = 4 * F * a i := by
  fin_cases i
  · change (∑ j : Fin 4, B 0 j * G j) = 4 * F * a 0
    simp only [Fin.sum_univ_four, B, a, C_factored, G_formula]
    norm_num [C₀, D, H₀, S, F]
    ring
  · change (∑ j : Fin 4, B 1 j * G j) = 4 * F * a 1
    simp only [Fin.sum_univ_four, B, a, C_factored, G_formula]
    norm_num [C₀, D, H₀, S, F]
    ring
  · change (∑ j : Fin 4, B 2 j * G j) = 4 * F * a 2
    simp only [Fin.sum_univ_four, B, a, C_factored, G_formula]
    norm_num [C₀, D, H₀, S, F]
    ring
  · change (∑ j : Fin 4, B 3 j * G j) = 4 * F * a 3
    simp only [Fin.sum_univ_four, B, a, C_factored, G_formula]
    norm_num [C₀, D, H₀, S, F]
    ring

theorem QP_F_zero : QP F = 0 := by
  rw [QP_apply]
  change (∑ i : Fin 4, ∑ j : Fin 4, B i j * H i j) +
    6 * (∑ i : Fin 4, a i * G i) = 0
  rw [H_formula]
  simp only [Fin.sum_univ_four, B, a, C_factored, G_formula]
  norm_num [C₀, D, H₀, S, Fin.succAbove, Fin.ext_iff]
  ring

#print axioms NakaiQuartic.B_mul_G
#print axioms NakaiQuartic.QP_F_zero
end NakaiQuartic
