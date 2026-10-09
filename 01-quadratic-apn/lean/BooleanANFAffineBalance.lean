import BooleanANFDescent
import BooleanANFStabilizer

namespace BooleanANF
open scoped BigOperators

/-- Tiny finite consequence of the affine-function stabilizer count. -/
theorem affine_five_stabilizer_arithmetic (w h : ℕ)
    (hw : w ≤ 32) (hh : h ≤ 32) (hdiv : h ∣ 32)
    (he : (32 : ℤ) * (32 - h) = 2 * w * (32 - w)) :
    w = 0 ∨ w = 16 ∨ w = 32 := by
  have checked : ∀ w : Fin 33, ∀ h : Fin 33,
      h.val ∣ 32 →
      (32 : ℤ) * (32 - h.val) = 2 * w.val * (32 - w.val) →
      w.val = 0 ∨ w.val = 16 ∨ w.val = 32 := by decide
  exact checked ⟨w, by omega⟩ ⟨h, by omega⟩ hdiv he

/-- Derivatives of an actual affine Boolean function are constant, here counted
through the degree-zero quotient of the concrete derivative descent. -/
theorem affine_five_derivative_weights {f : (Fin 5 → F₂) → F₂}
    (hf : HasDegreeLE f 1) (a : Fin 5 → F₂) :
    weight (derivative f a) = 0 ∨ weight (derivative f a) = 32 := by
  by_cases ha : a = 0
  · subst a
    left
    simp [derivative, CharTwo.add_self_eq_zero, weight]
  · obtain ⟨g, hg, he, hle⟩ := derivative_descent 4 0 f hf a ha
    have hwg : weight g = 16 * (g 0).val := by
      have hfun : g = fun _ => g 0 := funext hg.eq_const
      calc
        weight g = weight (fun _ : Fin 4 → F₂ => g 0) := congrArg weight hfun
        _ = 16 * (g 0).val := by simp [weight, Fintype.card_fun, ZMod.card]
    have hc : g 0 = 0 ∨ g 0 = 1 := by
      generalize g 0 = c
      fin_cases c <;> simp_all
    rcases hc with hc | hc <;> norm_num [hc, ZMod.val_one_eq_one_mod] at hwg <;> omega

/-- The actual affine-five spectrum, derived from degree-zero derivatives and
translation-stabilizer counting rather than an assumed rank classification. -/
theorem affine_five_weights {f : (Fin 5 → F₂) → F₂}
    (hf : HasDegreeLE f 1) : weight f = 0 ∨ weight f = 16 ∨ weight f = 32 := by
  have hw := weight_le_card f
  have hh := translationStabilizer_card_le f
  have hd := translationStabilizer_card_dvd f
  have he := derivative_stabilizer_count f 32 (affine_five_derivative_weights hf)
  norm_num only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at hw hh hd he
  exact affine_five_stabilizer_arithmetic (weight f)
    (Nat.card (translationStabilizer f)) hw hh hd he

end BooleanANF
