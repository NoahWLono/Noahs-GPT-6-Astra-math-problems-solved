import FreshSampling

/-! Event-weighted guarantees for one preselected interruption threshold.
This is a joint probability bound, not a bound conditioned on `T=t`. -/
namespace ProgressivePool.FreshSampling
open Finset Classical
variable {A : Type*}

/-- Restricting the prior weights to the event `T=t` yields the exact joint
acceptance mass.  Its good-state contribution is weighted by `Pr[T=t]`; its
bad-state contribution is bounded by the original bad-state probability. -/
theorem fresh_joint_threshold {s u : ℕ} (hs : 0 < s)
    (states : Finset A) (weights : A → ℚ) (K : A → Finset (Fin s))
    (T : A → ℕ) (bad : A → Prop) (t : ℕ)
    (hw : ∀ a ∈ states, 0 ≤ weights a)
    (hgood : ∀ a ∈ states, ¬ bad a → (K a).card ≤ u - 1) :
    acceptMass states (fun a => if T a = t then weights a else 0) K T ≤
      ((((u - 1 : ℕ) : ℚ) / (s : ℚ)) ^ t) *
        (∑ a ∈ states.filter (fun a => T a = t), weights a) +
      ∑ a ∈ states.filter bad, weights a := by
  classical
  have hrestricted : ∀ a ∈ states, 0 ≤ (if T a = t then weights a else 0) := by
    intro a ha
    split
    · exact hw a ha
    · exact le_refl _
  have h := fresh_threshold_mixture hs states
    (fun a => if T a = t then weights a else 0) K T bad hrestricted hgood
  have he : (∑ a ∈ states, (if T a = t then weights a else 0) *
      ((((u - 1 : ℕ) : ℚ) / (s : ℚ)) ^ T a)) =
      ((((u - 1 : ℕ) : ℚ) / (s : ℚ)) ^ t) *
        (∑ a ∈ states.filter (fun a => T a = t), weights a) := by
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro a ha
    by_cases ht : T a = t <;> simp [ht, mul_comm]
  have hb : (∑ a ∈ states.filter bad, if T a = t then weights a else 0) ≤
      ∑ a ∈ states.filter bad, weights a := by
    apply sum_le_sum
    intro a ha
    split
    · exact le_refl _
    · exact hw a (mem_filter.mp ha).1
  rw [he] at h
  exact h.trans (add_le_add_left hb _)

/-- Uniform-root form of the joint event bound. -/
theorem fresh_joint_threshold_uniform {s u : ℕ} (hs : 0 < s)
    (states : Finset A) (K : A → Finset (Fin s)) (T : A → ℕ)
    (bad : A → Prop) (t : ℕ)
    (hgood : ∀ a ∈ states, ¬ bad a → (K a).card ≤ u - 1) :
    acceptMass states (fun a => if T a = t then 1 / (states.card : ℚ) else 0) K T ≤
      ((((u - 1 : ℕ) : ℚ) / (s : ℚ)) ^ t) *
        (((states.filter (fun a => T a = t)).card : ℚ) / (states.card : ℚ)) +
      ((states.filter bad).card : ℚ) / (states.card : ℚ) := by
  have h := fresh_joint_threshold hs states (fun _ => 1 / (states.card : ℚ))
    K T bad t (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)) hgood
  simpa [nsmul_eq_mul, div_eq_mul_inv] using h

#print axioms fresh_joint_threshold
#print axioms fresh_joint_threshold_uniform
end ProgressivePool.FreshSampling
