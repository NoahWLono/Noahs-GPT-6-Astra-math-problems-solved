import BooleanANFDivisibility
import BooleanANFDescentSpec

set_option maxRecDepth 2048
set_option maxHeartbeats 1200000

namespace BooleanANF
open scoped BigOperators

/-- Assembly lemma, explicitly conditional on the two remaining semantic
prerequisites. It is not asserted to be an unconditional spectrum theorem. -/
theorem cubic_seven_low_weight_of_descent
    (descent : DerivativeDescent 6 2)
    (quadratic : ∀ q : (Fin 6 → F₂) → F₂,
      HasDegreeLE q 2 → weight q < 24 → weight q = 0 ∨ weight q = 16)
    {f : (Fin 7 → F₂) → F₂} (hf : HasDegreeLE f 3)
    (hw : weight f ≤ 26) : weight f = 0 ∨ weight f = 16 ∨ weight f = 24 := by
  have hm := cubic_seven_weight_mod_four hf
  have hs := derivative_weight_sum f
  norm_num [Fintype.card_fun, ZMod.card] at hs
  have hd (a : Fin 7 → F₂) (hlt : weight f < 24) :
      weight (derivative f a) = 0 ∨ weight (derivative f a) = 32 := by
    by_cases ha : a = 0
    · left
      subst a
      simp [derivative, CharTwo.add_self_eq_zero, weight]
    · obtain ⟨q, hq, he, hle⟩ := descent f hf a ha
      rcases quadratic q hq (by omega) with h | h <;> omega
  have hsmall (hlt : weight f < 16) : weight f = 0 := by
    have hz (a : Fin 7 → F₂) : weight (derivative f a) = 0 := by
      by_cases ha : a = 0
      · subst a
        simp [derivative, CharTwo.add_self_eq_zero, weight]
      · obtain ⟨q, hq, he, hle⟩ := descent f hf a ha
        rcases quadratic q hq (by omega) with h | h <;> omega
    simp only [hz, Nat.cast_zero, Finset.sum_const_zero] at hs
    have hn : (0 : ℤ) ≤ weight f := Int.natCast_nonneg _
    have hl : (weight f : ℤ) < 16 := by exact_mod_cast hlt
    have he : (weight f : ℤ) = 0 := by nlinarith
    exact_mod_cast he
  have hnot20 : weight f ≠ 20 := by
    intro he
    have hb (a : Fin 7 → F₂) : (weight (derivative f a) : ℤ) ≤ 32 := by
      rcases hd a (by omega) with h | h <;> simp [h]
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hb a)
    norm_num [Fintype.card_fun, ZMod.card] at hsum
    rw [hs, he] at hsum
    norm_num at hsum
  by_cases hl : weight f < 16
  · exact Or.inl (hsmall hl)
  · omega

/-- Final modular obstruction for actual Boolean functions, with the cubic
spectrum and derivative-coordinate descent displayed as explicit premises. -/
theorem quartic_eight_residue_bound_of_descent
    (descent : DerivativeDescent 7 3)
    (cubic : ∀ g : (Fin 7 → F₂) → F₂,
      HasDegreeLE g 3 → weight g ≤ 26 →
        weight g = 0 ∨ weight g = 16 ∨ weight g = 24)
    {f : (Fin 8 → F₂) → F₂} (hf : HasDegreeLE f 4)
    (hr : weight f % 4 = 2) : 30 ≤ weight f := by
  by_contra hn
  have hw : weight f ≤ 26 := by omega
  have hd (a : Fin 8 → F₂) : (16 : ℤ) ∣ (weight (derivative f a) : ℤ) := by
    by_cases ha : a = 0
    · subst a
      simp [derivative, CharTwo.add_self_eq_zero, weight]
    · obtain ⟨g, hg, he, hle⟩ := descent f hf a ha
      rcases cubic g hg (by omega) with h | h | h <;> rw [h] at he <;>
        norm_num [he]
  have hsum : (16 : ℤ) ∣ ∑ a : Fin 8 → F₂, (weight (derivative f a) : ℤ) :=
    Finset.dvd_sum (fun a _ => hd a)
  rw [derivative_weight_sum] at hsum
  norm_num [Fintype.card_fun, ZMod.card] at hsum
  interval_cases he : weight f <;> norm_num [he] at hr hsum

end BooleanANF
