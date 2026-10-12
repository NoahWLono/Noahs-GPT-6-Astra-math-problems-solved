import QuarticCoefficientDefinitions
noncomputable section
namespace NakaiQuartic
open MvPolynomial
open scoped BigOperators

theorem separator_G_mul (i : Fin 4) (p : P) : separator (G i * p) = 0 := by
  fin_cases i
  · change separator (G 0 * p) = 0
    rw [G0_monomials]
    simp only [add_mul, smul_mul_assoc, map_add, map_smul, separator,
      LinearMap.add_apply, LinearMap.smul_apply, lcoeff_apply,
      coeff_add, coeff_smul, coeff_monomial_mul', exp4_sub, exp4_le, smul_eq_mul]
    norm_num
    ring
  · change separator (G 1 * p) = 0
    rw [G1_monomials]
    simp only [add_mul, smul_mul_assoc, map_add, map_smul, separator,
      LinearMap.add_apply, LinearMap.smul_apply, lcoeff_apply,
      coeff_add, coeff_smul, coeff_monomial_mul', exp4_sub, exp4_le, smul_eq_mul]
    norm_num
    ring
  · change separator (G 2 * p) = 0
    rw [G2_monomials]
    simp only [add_mul, smul_mul_assoc, map_add, map_smul, separator,
      LinearMap.add_apply, LinearMap.smul_apply, lcoeff_apply,
      coeff_add, coeff_smul, coeff_monomial_mul', exp4_sub, exp4_le, smul_eq_mul]
    norm_num
    ring
  · change separator (G 3 * p) = 0
    rw [G3_monomials]
    simp only [add_mul, smul_mul_assoc, map_add, map_smul, separator,
      LinearMap.add_apply, LinearMap.smul_apply, lcoeff_apply,
      coeff_add, coeff_smul, coeff_monomial_mul', exp4_sub, exp4_le, smul_eq_mul]
    norm_num
    ring


#print axioms NakaiQuartic.separator_G_mul
end NakaiQuartic
