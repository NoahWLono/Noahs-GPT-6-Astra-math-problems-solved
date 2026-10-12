import QuarticSeparatorMonomials
import QuarticDeterminant
noncomputable section
namespace NakaiQuartic
open MvPolynomial
open scoped BigOperators

theorem separator_h : separator h = -77760 := by
  rw [h_monomials]
  simp only [map_add, map_smul,
    separator_monomial_0, separator_monomial_1, separator_monomial_2, separator_monomial_3, separator_monomial_4, separator_monomial_5, separator_monomial_6, separator_monomial_7, separator_monomial_8, separator_monomial_9, separator_monomial_10, separator_monomial_11, separator_monomial_12, separator_monomial_13, separator_monomial_14, separator_monomial_15, separator_monomial_16, separator_monomial_17, separator_monomial_18, separator_monomial_19, separator_monomial_20, separator_monomial_21, separator_monomial_22, separator_monomial_23, separator_monomial_24, separator_monomial_25, separator_monomial_26, separator_monomial_27, separator_monomial_28, separator_monomial_29, separator_monomial_30, separator_monomial_31, separator_monomial_32, separator_monomial_33, separator_monomial_34]
  norm_num


#print axioms NakaiQuartic.separator_h
end NakaiQuartic
