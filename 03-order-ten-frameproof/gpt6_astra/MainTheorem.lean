import CanonicalMatrix
import FiniteCase2
import FiniteCase3
import FiniteCase4
import FiniteCase5

set_option autoImplicit false

namespace GPT6Astra

/-- Every binary order-ten separating hash family of type {1,3} is a
permutation matrix up to independent complementation of its rows. -/
theorem every_order_ten_shf_is_trivial (A : BinaryMatrix 10) (h : IsSHF A) :
    IsTrivial A := by
  classical
  by_contra hnt
  obtain ⟨k, B, hk2, hk5, hB, hfixed, hanchor, hrows, hcols⟩ :=
    exists_anchored_canonical_matrix A h hnt
  interval_cases k
  · exact anchored_case_2 B hB hfixed hanchor hrows hcols
  · exact anchored_case_3 B hB hfixed hanchor hrows hcols
  · exact anchored_case_4 B hB hfixed hanchor hrows hcols
  · exact anchored_case_5 B hB hfixed hanchor hrows hcols

/-- Negative resolution of the existential order-ten question formalized in
`OpenProblem10`. The theorem has no additional mathematical hypotheses. -/
theorem not_openProblem10 : ¬ OpenProblem10 := by
  rintro ⟨A, hA, hnt⟩
  exact hnt (every_order_ten_shf_is_trivial A hA)

end GPT6Astra

#print GPT6Astra.every_order_ten_shf_is_trivial
#print GPT6Astra.not_openProblem10
#print axioms GPT6Astra.every_order_ten_shf_is_trivial
#print axioms GPT6Astra.not_openProblem10
