import QuarticCoefficientDefinitions
noncomputable section
namespace NakaiQuartic
open MvPolynomial

theorem separator_monomial_0 : separator (monomial (exp4 8 0 0 0) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_1 : separator (monomial (exp4 6 2 0 0) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_2 : separator (monomial (exp4 6 0 2 0) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_3 : separator (monomial (exp4 6 0 0 2) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_4 : separator (monomial (exp4 4 4 0 0) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_5 : separator (monomial (exp4 4 2 2 0) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_6 : separator (monomial (exp4 4 2 0 2) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_7 : separator (monomial (exp4 4 0 4 0) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_8 : separator (monomial (exp4 4 0 2 2) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_9 : separator (monomial (exp4 4 0 0 4) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_10 : separator (monomial (exp4 2 6 0 0) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_11 : separator (monomial (exp4 2 4 2 0) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_12 : separator (monomial (exp4 2 4 0 2) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_13 : separator (monomial (exp4 2 2 4 0) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_14 : separator (monomial (exp4 2 2 2 2) (1 : ℚ)) = -12 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_15 : separator (monomial (exp4 2 2 0 4) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_16 : separator (monomial (exp4 2 0 6 0) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_17 : separator (monomial (exp4 2 0 4 2) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_18 : separator (monomial (exp4 2 0 2 4) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_19 : separator (monomial (exp4 2 0 0 6) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_20 : separator (monomial (exp4 0 8 0 0) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_21 : separator (monomial (exp4 0 6 2 0) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_22 : separator (monomial (exp4 0 6 0 2) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_23 : separator (monomial (exp4 0 4 4 0) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_24 : separator (monomial (exp4 0 4 2 2) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_25 : separator (monomial (exp4 0 4 0 4) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_26 : separator (monomial (exp4 0 2 6 0) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_27 : separator (monomial (exp4 0 2 4 2) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_28 : separator (monomial (exp4 0 2 2 4) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_29 : separator (monomial (exp4 0 2 0 6) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_30 : separator (monomial (exp4 0 0 8 0) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_31 : separator (monomial (exp4 0 0 6 2) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_32 : separator (monomial (exp4 0 0 4 4) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_33 : separator (monomial (exp4 0 0 2 6) (1 : ℚ)) = -2 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

theorem separator_monomial_34 : separator (monomial (exp4 0 0 0 8) (1 : ℚ)) = 3 := by
  simp only [separator, LinearMap.add_apply, LinearMap.smul_apply,
    lcoeff_apply, coeff_monomial, exp4_eq, smul_eq_mul]
  norm_num

#print axioms NakaiQuartic.separator_monomial_34
end NakaiQuartic
