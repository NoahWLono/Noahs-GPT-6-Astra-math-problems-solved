import QuarticCofactors
noncomputable section
namespace NakaiQuartic
open MvPolynomial
open scoped BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

theorem h_cofactor : h = ∑ j : Fin 4, H₀ 0 j * C j 0 := by
  simpa only [h, C, H_formula] using Matrix.det_eq_sum_mul_adjugate_row H 0

/-- Full degree-eight determinant expansion, checked as a polynomial identity. -/
theorem h_monomials : h =
  (96 : ℚ) • (monomial (exp4 8 0 0 0) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 6 2 0 0) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 6 0 2 0) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 6 0 0 2) (1 : ℚ)) +
  (1248 : ℚ) • (monomial (exp4 4 4 0 0) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 4 2 2 0) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 4 2 0 2) (1 : ℚ)) +
  (1248 : ℚ) • (monomial (exp4 4 0 4 0) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 4 0 2 2) (1 : ℚ)) +
  (1248 : ℚ) • (monomial (exp4 4 0 0 4) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 2 6 0 0) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 2 4 2 0) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 2 4 0 2) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 2 2 4 0) (1 : ℚ)) +
  (16272 : ℚ) • (monomial (exp4 2 2 2 2) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 2 2 0 4) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 2 0 6 0) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 2 0 4 2) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 2 0 2 4) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 2 0 0 6) (1 : ℚ)) +
  (96 : ℚ) • (monomial (exp4 0 8 0 0) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 0 6 2 0) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 0 6 0 2) (1 : ℚ)) +
  (1248 : ℚ) • (monomial (exp4 0 4 4 0) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 0 4 2 2) (1 : ℚ)) +
  (1248 : ℚ) • (monomial (exp4 0 4 0 4) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 0 2 6 0) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 0 2 4 2) (1 : ℚ)) +
  (4128 : ℚ) • (monomial (exp4 0 2 2 4) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 0 2 0 6) (1 : ℚ)) +
  (96 : ℚ) • (monomial (exp4 0 0 8 0) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 0 0 6 2) (1 : ℚ)) +
  (1248 : ℚ) • (monomial (exp4 0 0 4 4) (1 : ℚ)) +
  (720 : ℚ) • (monomial (exp4 0 0 2 6) (1 : ℚ)) +
  (96 : ℚ) • (monomial (exp4 0 0 0 8) (1 : ℚ)) := by
  rw [h_cofactor]
  simp only [Fin.sum_univ_four, C_factored, monomial_exp4, Algebra.smul_def, map_natCast, map_ofNat]
  norm_num [C₀, D, H₀, S, Fin.succAbove, Fin.ext_iff]
  ring


#print axioms NakaiQuartic.h_monomials
end NakaiQuartic
