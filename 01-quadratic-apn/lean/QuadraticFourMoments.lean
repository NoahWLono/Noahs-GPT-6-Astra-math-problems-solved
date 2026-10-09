import QuadraticFourPlane

namespace BooleanANF.QuadraticFour
open scoped BigOperators

/-- Every quadratic binary four-cube word has zero vector-valued first moment.
This is the coefficient cancellation needed by the d=1 affine-graph shortcut. -/
theorem quadratic_first_moment_zero {f : V → F₂} (hf : HasDegreeLE f 2) :
    (∑ x : V, f x • x) = 0 := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← coefficient_top_eq_sum]
  exact (hf.mul (degree_coordinate i)) _ (by norm_num)

#print axioms quadratic_first_moment_zero
end BooleanANF.QuadraticFour
