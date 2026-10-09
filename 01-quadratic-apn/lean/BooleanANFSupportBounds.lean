import BooleanANFDerivativeWeight

namespace BooleanANF
open scoped BigOperators
variable {A : Type*} [Fintype A]

/-- Support weight never exceeds the size of the domain. -/
theorem weight_le_card (f : A → F₂) : weight f ≤ Fintype.card A := by
  have hb (x : A) : (f x).val ≤ 1 := by
    have h := (f x).val_lt
    omega
  have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hb x)
  simpa [weight] using h

/-- Zero support cardinality characterizes the zero function. -/
theorem weight_eq_zero_iff (f : A → F₂) : weight f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hz : ∀ x : A, (f x).val = 0 := by
      exact fun x => (Finset.sum_eq_zero_iff.mp h) x (Finset.mem_univ x)
    funext x
    exact (ZMod.val_eq_zero (f x)).mp (hz x)
  · rintro rfl
    simp [weight]

/-- The symmetric difference with a translate has at most twice the support. -/
theorem weight_derivative_le [AddGroup A] (f : A → F₂) (a : A) :
    weight (derivative f a) ≤ 2 * weight f := by
  have h := weight_add (fun x => f (x+a)) f
  rw [weight_translate] at h
  have hn : (0 : ℤ) ≤ weight (fun x => f (x+a) * f x) := Int.natCast_nonneg _
  change (weight (derivative f a) : ℤ) = _ at h
  omega

end BooleanANF
