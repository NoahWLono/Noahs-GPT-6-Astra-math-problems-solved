import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Fresh uniform sampling after a finite adaptive experiment

For each prior state `a`, the length `T a` and zero set `K a` are fixed before
fresh samples are drawn.  Fresh draws are explicitly the uniform functions
`Fin (T a) → Fin s`; repeated indices are allowed.  For state-dependent lengths,
the outer mixture uses the prior state weights, not the uniform law on a
variable-size disjoint union.  Everything is expressed as exact finite counts
or rational finite sums.
-/
namespace ProgressivePool.FreshSampling
open Finset Classical

/-- All fresh index strings that land in the zero set. -/
noncomputable def allHit {s : ℕ} (K : Finset (Fin s)) (t : ℕ) :
    Finset (Fin t → Fin s) :=
  univ.filter fun draws => ∀ i, draws i ∈ K

/-- The accepting fresh strings are exactly the finite Cartesian power. -/
theorem allHit_eq_pi {s : ℕ} (K : Finset (Fin s)) (t : ℕ) :
    allHit K t = Fintype.piFinset (fun _ : Fin t => K) := by
  ext draws
  simp [allHit, Fintype.mem_piFinset]

/-- Exact numerator of the fresh acceptance probability. -/
theorem allHit_card {s : ℕ} (K : Finset (Fin s)) (t : ℕ) :
    (allHit K t).card = K.card ^ t := by
  rw [allHit_eq_pi, Fintype.card_piFinset_const]

/-- Exact size of the fresh sample space. -/
theorem allDraws_card (s t : ℕ) :
    (univ : Finset (Fin t → Fin s)).card = s ^ t := by
  simp [Fintype.card_pi_const]

/-- Probability is defined directly by counting in the uniform fresh space. -/
noncomputable def acceptProbability {s : ℕ} (K : Finset (Fin s)) (t : ℕ) : ℚ :=
  (allHit K t).card / (univ : Finset (Fin t → Fin s)).card

theorem acceptProbability_eq {s : ℕ} (K : Finset (Fin s)) (t : ℕ) :
    acceptProbability K t = ((K.card : ℚ) / (s : ℚ)) ^ t := by
  rw [acceptProbability, allHit_card, allDraws_card]
  simp [div_pow]

lemma acceptProbability_nonneg {s : ℕ} (K : Finset (Fin s)) (t : ℕ) :
    0 ≤ acceptProbability K t := by
  rw [acceptProbability_eq]
  exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

lemma acceptProbability_le_one {s : ℕ} (hs : 0 < s)
    (K : Finset (Fin s)) (t : ℕ) : acceptProbability K t ≤ 1 := by
  rw [acceptProbability_eq]
  have hcard : K.card ≤ s := by simpa using card_le_univ K
  apply pow_le_one₀ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  apply (div_le_one₀ (Nat.cast_pos.mpr hs)).mpr
  exact Nat.cast_le.mpr hcard

lemma acceptProbability_le_threshold {s r : ℕ} (K : Finset (Fin s))
    (t : ℕ) (hK : K.card ≤ r) :
    acceptProbability K t ≤ ((r : ℚ) / (s : ℚ)) ^ t := by
  rw [acceptProbability_eq]
  apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hK) (Nat.cast_nonneg _)

variable {A : Type*}

/-- Exact accepting mass of the fresh experiment.  Each atom `(a, draws)` has
mass `weights a / s^(T a)`.  The prior state determines `T` before drawing. -/
noncomputable def acceptMass {s : ℕ} (states : Finset A) (weights : A → ℚ)
    (K : A → Finset (Fin s)) (T : A → ℕ) : ℚ :=
  ∑ a ∈ states, ∑ _draws ∈ allHit (K a) (T a), weights a / (s : ℚ) ^ T a

/-- Total mass on the explicit state/fresh-draw experiment. -/
noncomputable def sampleMass (s : ℕ) (states : Finset A) (weights : A → ℚ)
    (T : A → ℕ) : ℚ :=
  ∑ a ∈ states, ∑ _draws ∈ (univ : Finset (Fin (T a) → Fin s)),
    weights a / (s : ℚ) ^ T a

/-- Fresh uniform sampling preserves exactly the prior state mass. -/
theorem sampleMass_eq {s : ℕ} (hs : 0 < s) (states : Finset A)
    (weights : A → ℚ) (T : A → ℕ) :
    sampleMass s states weights T = ∑ a ∈ states, weights a := by
  unfold sampleMass
  apply sum_congr rfl
  intro a ha
  have hden : (s : ℚ) ^ T a ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs))
  simp [allDraws_card, nsmul_eq_mul, mul_div_assoc, mul_comm, hden]
  exact mul_div_cancel₀ _ hden

/-- Counting the inner fresh strings gives the exact conditional mixture. -/
theorem acceptMass_eq {s : ℕ} (states : Finset A) (weights : A → ℚ)
    (K : A → Finset (Fin s)) (T : A → ℕ) :
    acceptMass states weights K T =
      ∑ a ∈ states, weights a * acceptProbability (K a) (T a) := by
  apply sum_congr rfl
  intro a ha
  simp [acceptMass, acceptProbability, allHit_card, allDraws_card,
    nsmul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- Finite-mixture threshold bound.  Nonnegative prior weights need not be
normalized for this inequality.  When they sum to one, the last sum is exactly
the probability of the bad-state event. -/
theorem fresh_threshold_mixture {s u : ℕ} (hs : 0 < s)
    (states : Finset A) (weights : A → ℚ) (K : A → Finset (Fin s))
    (T : A → ℕ) (bad : A → Prop)
    (hw : ∀ a ∈ states, 0 ≤ weights a)
    (hgood : ∀ a ∈ states, ¬ bad a → (K a).card ≤ u - 1) :
    acceptMass states weights K T ≤
      (∑ a ∈ states, weights a * (((u - 1 : ℕ) : ℚ) / (s : ℚ)) ^ T a) +
      ∑ a ∈ states.filter bad, weights a := by
  classical
  rw [acceptMass_eq, sum_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro a ha
  by_cases hb : bad a
  · simp only [hb, ite_true]
    have hp := mul_le_mul_of_nonneg_left (acceptProbability_le_one hs (K a) (T a))
      (hw a ha)
    have hterm : 0 ≤ weights a * (((u - 1 : ℕ) : ℚ) / (s : ℚ)) ^ T a :=
      mul_nonneg (hw a ha) (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)
    calc
      _ ≤ weights a := by simpa using hp
      _ ≤ _ := le_add_of_nonneg_left hterm
  · simp only [hb, ite_false, add_zero]
    exact mul_le_mul_of_nonneg_left
      (acceptProbability_le_threshold (K a) (T a) (hgood a ha hb)) (hw a ha)

/-- Uniform prior-state specialization.  For a nonempty `states`, the first
term is the expectation of the preselected random-threshold power, and the
second term is the bad-state probability. -/
theorem fresh_threshold_uniform {s u : ℕ} (hs : 0 < s)
    (states : Finset A) (K : A → Finset (Fin s)) (T : A → ℕ)
    (bad : A → Prop)
    (hgood : ∀ a ∈ states, ¬ bad a → (K a).card ≤ u - 1) :
    acceptMass states (fun _ => 1 / (states.card : ℚ)) K T ≤
      (∑ a ∈ states, (((u - 1 : ℕ) : ℚ) / (s : ℚ)) ^ T a) /
        (states.card : ℚ) +
      ((states.filter bad).card : ℚ) / (states.card : ℚ) := by
  classical
  have h := fresh_threshold_mixture hs states (fun _ => 1 / (states.card : ℚ))
    K T bad (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)) hgood
  simpa [one_div, ← mul_sum, nsmul_eq_mul, div_eq_mul_inv, mul_comm] using h

#print axioms allHit_card
#print axioms allDraws_card
#print axioms sampleMass_eq
#print axioms acceptMass_eq
#print axioms fresh_threshold_mixture
#print axioms fresh_threshold_uniform
end ProgressivePool.FreshSampling
