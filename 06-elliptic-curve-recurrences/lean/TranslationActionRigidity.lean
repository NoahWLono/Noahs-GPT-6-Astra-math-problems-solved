import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra

/-! An exceptional-point extension lemma for an actual additive action.
Its auxiliary-point premise will be supplied by the checked elliptic doubling-fiber theorem. -/
namespace Astra01
section
variable {A : Type*} [AddCommGroup A] [Infinite A]
variable (σ : A → Equiv.Perm A)
variable (hzero : ∀ P, σ 0 P = P)
variable (hadd : ∀ G H P, σ (G + H) P = σ G (σ H P))
variable (hgeneric : ∀ G P, P ≠ 0 → P ≠ G → P ≠ -G → σ G P = P + G)
variable (haux : ∀ P R : A, ∃ Q : A, Q ≠ 0 ∧ (2 : ℕ) • Q ≠ P ∧ (2 : ℕ) • Q ≠ R)

include hadd hgeneric haux in
theorem translation_action_regular (G P : A) (hP : P ≠ 0) (hPG : P + G ≠ 0) :
    σ G P = P + G := by
  obtain ⟨Q, hQ, hQP, hQPG⟩ := haux P (P + G)
  let H := P - Q
  have hQH : Q ≠ H := by
    intro h
    apply hQP
    simpa only [two_nsmul] using (eq_sub_iff_add_eq.mp h)
  have hQnH : Q ≠ -H := by
    intro h
    apply hP
    have he : Q = Q - P := by simpa only [H, neg_sub] using h
    exact sub_eq_self.mp he.symm
  have hQGH : Q ≠ G + H := by
    intro h
    apply hQPG
    have he : Q = (G + P) - Q := by simpa only [H, add_sub_assoc] using h
    simpa only [two_nsmul, add_comm G P] using (eq_sub_iff_add_eq.mp he)
  have hQnGH : Q ≠ -(G + H) := by
    intro h
    apply hPG
    have he : Q = Q - (G + P) := h.trans (by dsimp only [H]; abel)
    have hz := sub_eq_self.mp he.symm
    simpa only [add_comm] using hz
  have hHQ : σ H Q = P := by
    rw [hgeneric H Q hQ hQH hQnH]
    dsimp only [H]
    abel
  calc
    σ G P = σ G (σ H Q) := congrArg (σ G) hHQ.symm
    _ = σ (G + H) Q := (hadd G H Q).symm
    _ = Q + (G + H) := hgeneric (G + H) Q hQ hQGH hQnGH
    _ = P + G := by dsimp only [H]; abel

include hadd hgeneric haux in
theorem translation_action_zero_cases (G : A) : σ G 0 = 0 ∨ σ G 0 = G := by
  by_contra! hn
  let P := σ G 0 - G
  have hP : P ≠ 0 := sub_ne_zero.mpr hn.2
  have hPG : P + G ≠ 0 := by simpa only [P, sub_add_cancel] using hn.1
  have he := translation_action_regular σ hadd hgeneric haux G P hP hPG
  have hP0 : P = 0 := (σ G).injective (by simpa only [P, sub_add_cancel] using he)
  exact hP hP0

include hadd hgeneric haux in
theorem translation_action_neg_cases (G : A) : σ G (-G) = 0 ∨ σ G (-G) = G := by
  by_contra! hn
  let P := σ G (-G) - G
  have hP : P ≠ 0 := sub_ne_zero.mpr hn.2
  have hPG : P + G ≠ 0 := by simpa only [P, sub_add_cancel] using hn.1
  have he := translation_action_regular σ hadd hgeneric haux G P hP hPG
  have hPn : P = -G := (σ G).injective (by simpa only [P, sub_add_cancel] using he)
  have hz : σ G (-G) = 0 := by
    have hh := congrArg (fun R => R + G) hPn
    simpa only [P, sub_add_cancel, neg_add_cancel] using hh
  exact hn.1 hz

include hzero hadd hgeneric haux in
theorem translation_action_zero (G : A) : σ G 0 = G := by
  by_cases hG : G = 0
  · subst G
    exact hzero 0
  obtain hz | hz := translation_action_zero_cases σ hadd hgeneric haux G
  · have hneg : σ G (-G) = G := by
      obtain hn | hn := translation_action_neg_cases σ hadd hgeneric haux G
      · have he := (σ G).injective (hn.trans hz.symm)
        exact False.elim (hG (neg_eq_zero.mp he))
      · exact hn
    obtain ⟨H, hH⟩ := (((Set.finite_singleton (-G)).insert G).insert 0).exists_notMem
    have hH0 : H ≠ 0 := by intro he; exact hH (by simp [he])
    have hHG : H ≠ G := by
      intro he
      exact hH (by simp [he])
    have hHn : H ≠ -G := by
      intro he
      exact hH (by simp [he])
    have ha : σ G (σ H (-G)) = H := by
      rw [translation_action_regular σ hadd hgeneric haux H (-G) (neg_ne_zero.mpr hG)
        (by intro he; exact hHG (eq_of_neg_add_eq_zero he).symm)]
      rw [translation_action_regular σ hadd hgeneric haux G (-G + H)
        (by intro he; exact hHG (eq_of_neg_add_eq_zero he).symm) (by simpa using hH0)]
      abel
    have hb : σ H (σ G (-G)) = G + H := by
      rw [hneg, translation_action_regular σ hadd hgeneric haux H G hG
        (by intro he; exact hHn (eq_neg_of_add_eq_zero_right he))]
    have hc : σ G (σ H (-G)) = σ H (σ G (-G)) := by
      rw [← hadd, ← hadd, add_comm G H]
    rw [ha, hb] at hc
    have : G = 0 := add_eq_right.mp hc.symm
    exact False.elim (hG this)
  · exact hz

include hzero hadd hgeneric haux in
theorem translation_action_rigidity (G P : A) : σ G P = P + G := by
  by_cases hP : P = 0
  · subst P
    simpa only [zero_add] using translation_action_zero σ hzero hadd hgeneric haux G
  by_cases hPG : P + G = 0
  · have hPn : P = -G := eq_neg_of_add_eq_zero_left hPG
    subst P
    have he := hadd G (-G) 0
    rw [add_neg_cancel, hzero, translation_action_zero σ hzero hadd hgeneric haux] at he
    simpa only [neg_add_cancel] using he.symm
  · exact translation_action_regular σ hadd hgeneric haux G P hP hPG

end
end Astra01
#print axioms Astra01.translation_action_rigidity
