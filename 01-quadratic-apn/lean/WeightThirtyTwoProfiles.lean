import WeightThirtyTwoPatterns

set_option maxHeartbeats 1600000
namespace BooleanANF
open scoped BigOperators

theorem rank_two_coefficient_profiles {q : DoubleBlock → F₂} (h : NormalizedQuartic q)
    (e : (Fin 2 → F₂) ≃ₗ[F₂] quadraticCoefficientSpace q) :
    let n10 := pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 1 0
    let n01 := pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 0 1
    let n11 := pairPatternCount (codeBasisWord e 0) (codeBasisWord e 1) 1 1
    (n10=2 ∧ n01=2 ∧ n11=2) ∨ (n10=1 ∧ n01=3 ∧ n11=3) ∨
    (n10=3 ∧ n01=1 ∧ n11=3) ∨ (n10=3 ∧ n01=3 ∧ n11=1) := by
  have hab : codeBasisWord e 0 + codeBasisWord e 1 ≠ 0 := by
    have hn : (![1,1] : Fin 2 → F₂) ≠ 0 := by
      intro hh
      have h0 := congrFun hh 0
      exact (one_ne_zero : (1 : F₂) ≠ 0) (by simpa using h0)
    have he : (e (![1,1] : Fin 2 → F₂)).val = codeBasisWord e 0 + codeBasisWord e 1 := by
      funext y
      rw [code_word_expansion]
      simp [Fin.sum_univ_two]
    rw [← he]
    exact code_word_ne_zero e hn
  exact coefficient_pair_patterns h.totalDegree h.activeBound
    (codeBasisWord e 0) (codeBasisWord e 1)
    (e (Pi.single 0 1)).property (e (Pi.single 1 1)).property
    (codeBasisWord_ne_zero e 0) (codeBasisWord_ne_zero e 1) hab

end BooleanANF
