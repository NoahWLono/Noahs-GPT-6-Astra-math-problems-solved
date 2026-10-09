import BooleanANFAffineBalance
import BooleanANFLowWeight

namespace BooleanANF

/-- Every quadratic function on six Boolean coordinates of weight below24
has weight0 or16. This is proved using actual derivative descent, affine balance,
and the cardinality of its genuine translation subgroup. -/
theorem quadratic_six_low_weights {q : (Fin 6 → F₂) → F₂}
    (hq : HasDegreeLE q 2) (hw : weight q < 24) :
    weight q = 0 ∨ weight q = 16 := by
  have hd (a : Fin 6 → F₂) :
      weight (derivative q a) = 0 ∨ weight (derivative q a) = 32 := by
    by_cases ha : a = 0
    · subst a
      left
      simp [derivative, CharTwo.add_self_eq_zero, weight]
    · obtain ⟨g, hg, he, hle⟩ := derivative_descent 5 1 q hq a ha
      rcases affine_five_weights hg with h | h | h <;> omega
  have hh := translationStabilizer_card_le q
  have hdiv := translationStabilizer_card_dvd q
  have he := derivative_stabilizer_count q 32 hd
  norm_num only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at hh hdiv he
  exact quadratic_six_stabilizer_arithmetic (weight q)
    (Nat.card (translationStabilizer q)) hw hh hdiv he

/-- The required low-weight cubic-seven spectrum, with every premise discharged. -/
theorem cubic_seven_low_weights {g : (Fin 7 → F₂) → F₂}
    (hg : HasDegreeLE g 3) (hw : weight g ≤ 26) :
    weight g = 0 ∨ weight g = 16 ∨ weight g = 24 :=
  cubic_seven_low_weight_of_descent (derivative_descent 6 2)
    (fun _ hq hqw => quadratic_six_low_weights hq hqw) hg hw

/-- Elementary eight-variable residue bound for actual canonical Boolean ANF.
No Reed-Muller weight-spectrum or second-weight theorem is assumed. -/
theorem quartic_eight_residue_bound {f : (Fin 8 → F₂) → F₂}
    (hf : HasDegreeLE f 4) (hr : weight f % 4 = 2) : 30 ≤ weight f :=
  quartic_eight_residue_bound_of_descent (derivative_descent 7 3)
    (fun _ hg hw => cubic_seven_low_weights hg hw) hf hr

end BooleanANF
