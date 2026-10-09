import WeightThirtyTwoProfiles
import WeightThirtyTwoSix
import WeightThirtyTwoSeven

set_option maxHeartbeats 1600000
namespace BooleanANF
open scoped BigOperators

/-- The two basis words and their sum are all nonzero, so the actual coefficient
patterns are exactly the checked six-row or seven-row profiles. -/
theorem rank_two_code_exclusion {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 2 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) : False := by
  have hp := rank_two_coefficient_profiles h e
  have ht := rank_two_pattern_total e
  rcases hp with hp | hp | hp | hp
  · exact rank_two_six_exclusion h e hp.1 hp.2.1 hp.2.2
  · exact rank_two_not_seven h e (by omega) (Or.inl hp.1)
      (Or.inr hp.2.1) (Or.inr hp.2.2)
  · exact rank_two_not_seven h e (by omega) (Or.inr hp.1)
      (Or.inl hp.2.1) (Or.inr hp.2.2)
  · exact rank_two_not_seven h e (by omega) (Or.inr hp.1)
      (Or.inr hp.2.1) (Or.inl hp.2.2)

/-- The actual normalized weight-thirty residual cannot have coefficient-code
dimension two. This closes the d=2 branch without any support classification axiom. -/
theorem weight_thirty_case_two {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 2) : False := by
  let e := codeEquiv (quadraticCoefficientSpace q) 2 hd
  exact rank_two_code_exclusion h e

#print axioms weight_thirty_case_two
end BooleanANF
