import QuarticDefinitions
noncomputable section
namespace NakaiQuartic
open MvPolynomial
open scoped BigOperators

/-- The specified degree-eight coefficient functional. All 35 even exponent
permutations are written explicitly, so no hidden finite search enters the proof. -/
def separator : P →ₗ[ℚ] ℚ :=
  (3 : ℚ) • lcoeff ℚ (exp4 8 0 0 0) +
  (-2 : ℚ) • lcoeff ℚ (exp4 6 2 0 0) +
  (-2 : ℚ) • lcoeff ℚ (exp4 6 0 2 0) +
  (-2 : ℚ) • lcoeff ℚ (exp4 6 0 0 2) +
  (-2 : ℚ) • lcoeff ℚ (exp4 4 4 0 0) +
  (3 : ℚ) • lcoeff ℚ (exp4 4 2 2 0) +
  (3 : ℚ) • lcoeff ℚ (exp4 4 2 0 2) +
  (-2 : ℚ) • lcoeff ℚ (exp4 4 0 4 0) +
  (3 : ℚ) • lcoeff ℚ (exp4 4 0 2 2) +
  (-2 : ℚ) • lcoeff ℚ (exp4 4 0 0 4) +
  (-2 : ℚ) • lcoeff ℚ (exp4 2 6 0 0) +
  (3 : ℚ) • lcoeff ℚ (exp4 2 4 2 0) +
  (3 : ℚ) • lcoeff ℚ (exp4 2 4 0 2) +
  (3 : ℚ) • lcoeff ℚ (exp4 2 2 4 0) +
  (-12 : ℚ) • lcoeff ℚ (exp4 2 2 2 2) +
  (3 : ℚ) • lcoeff ℚ (exp4 2 2 0 4) +
  (-2 : ℚ) • lcoeff ℚ (exp4 2 0 6 0) +
  (3 : ℚ) • lcoeff ℚ (exp4 2 0 4 2) +
  (3 : ℚ) • lcoeff ℚ (exp4 2 0 2 4) +
  (-2 : ℚ) • lcoeff ℚ (exp4 2 0 0 6) +
  (3 : ℚ) • lcoeff ℚ (exp4 0 8 0 0) +
  (-2 : ℚ) • lcoeff ℚ (exp4 0 6 2 0) +
  (-2 : ℚ) • lcoeff ℚ (exp4 0 6 0 2) +
  (-2 : ℚ) • lcoeff ℚ (exp4 0 4 4 0) +
  (3 : ℚ) • lcoeff ℚ (exp4 0 4 2 2) +
  (-2 : ℚ) • lcoeff ℚ (exp4 0 4 0 4) +
  (-2 : ℚ) • lcoeff ℚ (exp4 0 2 6 0) +
  (3 : ℚ) • lcoeff ℚ (exp4 0 2 4 2) +
  (3 : ℚ) • lcoeff ℚ (exp4 0 2 2 4) +
  (-2 : ℚ) • lcoeff ℚ (exp4 0 2 0 6) +
  (3 : ℚ) • lcoeff ℚ (exp4 0 0 8 0) +
  (-2 : ℚ) • lcoeff ℚ (exp4 0 0 6 2) +
  (-2 : ℚ) • lcoeff ℚ (exp4 0 0 4 4) +
  (-2 : ℚ) • lcoeff ℚ (exp4 0 0 2 6) +
  (3 : ℚ) • lcoeff ℚ (exp4 0 0 0 8)

theorem G0_monomials : G 0 =
  (4 : ℚ) • (monomial (exp4 3 0 0 0) (1 : ℚ)) +
  (2 : ℚ) • (monomial (exp4 1 2 0 0) (1 : ℚ)) +
  (2 : ℚ) • (monomial (exp4 1 0 2 0) (1 : ℚ)) +
  (2 : ℚ) • (monomial (exp4 1 0 0 2) (1 : ℚ)) := by
  rw [G_formula]
  simp only [monomial_exp4, Algebra.smul_def, map_natCast, map_ofNat]
  simp only [S]
  ring

theorem G1_monomials : G 1 =
  (2 : ℚ) • (monomial (exp4 2 1 0 0) (1 : ℚ)) +
  (4 : ℚ) • (monomial (exp4 0 3 0 0) (1 : ℚ)) +
  (2 : ℚ) • (monomial (exp4 0 1 2 0) (1 : ℚ)) +
  (2 : ℚ) • (monomial (exp4 0 1 0 2) (1 : ℚ)) := by
  rw [G_formula]
  simp only [monomial_exp4, Algebra.smul_def, map_natCast, map_ofNat]
  simp only [S]
  ring

theorem G2_monomials : G 2 =
  (2 : ℚ) • (monomial (exp4 2 0 1 0) (1 : ℚ)) +
  (2 : ℚ) • (monomial (exp4 0 2 1 0) (1 : ℚ)) +
  (4 : ℚ) • (monomial (exp4 0 0 3 0) (1 : ℚ)) +
  (2 : ℚ) • (monomial (exp4 0 0 1 2) (1 : ℚ)) := by
  rw [G_formula]
  simp only [monomial_exp4, Algebra.smul_def, map_natCast, map_ofNat]
  simp only [S]
  ring

theorem G3_monomials : G 3 =
  (2 : ℚ) • (monomial (exp4 2 0 0 1) (1 : ℚ)) +
  (2 : ℚ) • (monomial (exp4 0 2 0 1) (1 : ℚ)) +
  (2 : ℚ) • (monomial (exp4 0 0 2 1) (1 : ℚ)) +
  (4 : ℚ) • (monomial (exp4 0 0 0 3) (1 : ℚ)) := by
  rw [G_formula]
  simp only [monomial_exp4, Algebra.smul_def, map_natCast, map_ofNat]
  simp only [S]
  ring


end NakaiQuartic
