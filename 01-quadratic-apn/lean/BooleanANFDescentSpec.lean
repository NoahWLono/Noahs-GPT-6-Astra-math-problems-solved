import BooleanANFDerivativeWeight

namespace BooleanANF

/-- Tiny finite arithmetic after the quadratic translation-stabilizer count.
Both divisibility and the exact count identity remain explicit premises. -/
theorem quadratic_six_stabilizer_arithmetic (w h : ℕ) (hw : w < 24)
    (hh : h ≤ 64) (hdiv : h ∣ 64)
    (he : (32 : ℤ) * (64 - h) = 2 * w * (64 - w)) :
    w = 0 ∨ w = 16 := by
  have checked : ∀ w : Fin 24, ∀ h : Fin 65,
      h.val ∣ 64 →
      (32 : ℤ) * (64 - h.val) = 2 * w.val * (64 - w.val) →
      w.val = 0 ∨ w.val = 16 := by decide
  exact checked ⟨w, hw⟩ ⟨h, by omega⟩ hdiv he

/-- The precise coordinate-descent obligation used in the low-weight proof. -/
def DerivativeDescent (n r : ℕ) : Prop :=
  ∀ f : (Fin (n+1) → F₂) → F₂, HasDegreeLE f (r+1) →
    ∀ a : Fin (n+1) → F₂, a ≠ 0 →
      ∃ g : (Fin n → F₂) → F₂, HasDegreeLE g r ∧
        weight (derivative f a) = 2 * weight g ∧ weight g ≤ weight f


end BooleanANF
