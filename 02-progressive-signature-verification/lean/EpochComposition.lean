import FreshSampling

/-!
# Composition over freshly sampled epochs

An epoch is an arbitrary deterministic map from its incoming history and a
fresh uniformly sampled finite bank to the next history, with a designated bad
bit.  Thus decisions about whether a final invocation occurs may depend on the
entire incoming history and on the epoch's bank.  Successive banks are modeled
by an explicit finite Cartesian product, with multiplied uniform atom weights.
This generic composition theorem does not verify a concrete pool state machine.
-/
namespace ProgressivePool.EpochComposition
open Finset Classical
universe u v

/-- Explicit product of `n` independent fresh bank samples. -/
def Samples (B : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => B × Samples B n

instance samplesFintype {B : Type u} [Fintype B] : (n : ℕ) → Fintype (Samples B n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 =>
      letI : Fintype (Samples B n) := samplesFintype (B := B) n
      inferInstanceAs (Fintype (B × Samples B n))

variable {B : Type u} [Fintype B] [Nonempty B]

/-- Each fresh bank contributes its exact uniform atom weight. -/
def sampleWeight : (n : ℕ) → Samples B n → ℚ
  | 0, _ => 1
  | n + 1, draws => (1 / (Fintype.card B : ℚ)) * sampleWeight n draws.2

omit [Nonempty B] in
lemma sampleWeight_nonneg (n : ℕ) (draws : Samples B n) :
    0 ≤ sampleWeight n draws := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih =>
      exact mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _)) (ih draws.2)

/-- Multiplying the fresh uniform factors gives a normalized finite law. -/
theorem sampleWeight_sum (n : ℕ) :
    (∑ draws : Samples B n, sampleWeight n draws) = 1 := by
  induction n with
  | zero => simp [Samples, sampleWeight]
  | succ n ih =>
      change (∑ draws : B × Samples B n,
        (1 / (Fintype.card B : ℚ)) * sampleWeight n draws.2) = 1
      rw [Fintype.sum_prod_type]
      simp [← mul_sum, ih, nsmul_eq_mul,
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos (α := B)))]

/-- Probability of an event in the explicit product sample space. -/
noncomputable def sampleProbability (n : ℕ) (event : Samples B n → Bool) : ℚ :=
  ∑ draws, if event draws then sampleWeight n draws else 0

omit [Nonempty B] in
lemma sampleProbability_nonneg (n : ℕ) (event : Samples B n → Bool) :
    0 ≤ sampleProbability n event := by
  apply sum_nonneg
  intro draws h
  split <;> simp_all [sampleWeight_nonneg]

omit [Nonempty B] in
lemma sampleProbability_mono (n : ℕ) (P Q : Samples B n → Bool)
    (hPQ : ∀ draws, P draws = true → Q draws = true) :
    sampleProbability n P ≤ sampleProbability n Q := by
  apply sum_le_sum
  intro draws h
  by_cases hp : P draws = true
  · simp [hp, hPQ draws hp]
  · simp only [hp, Bool.false_eq_true, if_false]
    split <;> simp_all [sampleWeight_nonneg]

variable {H : Type v}

/-- The designated bit can include an adaptive final-invocation decision. -/
structure Epoch (H : Type v) (B : Type u) where
  next : H → B → H
  bad : H → B → Bool

/-- Whether any designated bad event occurs on the realized finite run. -/
def anyBad : (epochs : List (Epoch H B)) → H → Samples B epochs.length → Bool
  | [], _, _ => false
  | e :: es, h, draws => e.bad h draws.1 || anyBad es (e.next h draws.1) draws.2

/-- Designated bad bit at one epoch; indices outside the run return false. -/
def badAt : (epochs : List (Epoch H B)) → H → Samples B epochs.length → ℕ → Bool
  | [], _, _, _ => false
  | e :: _, h, draws, 0 => e.bad h draws.1
  | e :: es, h, draws, n + 1 => badAt es (e.next h draws.1) draws.2 n

omit [Fintype B] [Nonempty B] in
lemma badAt_implies_any (epochs : List (Epoch H B)) (h : H)
    (draws : Samples B epochs.length) (n : ℕ)
    (hn : badAt epochs h draws n = true) : anyBad epochs h draws = true := by
  induction epochs generalizing h n with
  | nil => simp [badAt] at hn
  | cons e es ih =>
      cases n with
      | zero => simp [anyBad, badAt] at *; exact Or.inl hn
      | succ n =>
          simp only [anyBad, Bool.or_eq_true]
          exact Or.inr (ih _ draws.2 n hn)

/-- Exact recurrence obtained from the normalized fresh product law. -/
theorem anyBad_probability_cons (e : Epoch H B) (es : List (Epoch H B)) (h : H) :
    sampleProbability (e :: es).length (anyBad (e :: es) h) =
      (1 / (Fintype.card B : ℚ)) *
        ∑ b : B, if e.bad h b then 1 else
          sampleProbability es.length (anyBad es (e.next h b)) := by
  unfold sampleProbability
  change (∑ draws : B × Samples B es.length,
    if e.bad h draws.1 || anyBad es (e.next h draws.1) draws.2 then
      (1 / (Fintype.card B : ℚ)) * sampleWeight es.length draws.2 else 0) = _
  rw [Fintype.sum_prod_type, mul_sum]
  apply sum_congr rfl
  intro b hb
  by_cases hbad : e.bad h b = true
  · simp [hbad, ← mul_sum, sampleWeight_sum]
  · simp only [Bool.eq_false_iff.mpr hbad, Bool.false_or, Bool.false_eq_true, if_false]
    rw [mul_sum]
    apply sum_congr rfl
    intro draws hd
    split <;> simp_all

/-- Conditional bad mass derived from the number of bad fresh banks. -/
lemma local_count_to_probability (bad : B → Bool) (δ : ℚ)
    (hcount : ((univ.filter fun b => bad b = true).card : ℚ) ≤
      δ * (Fintype.card B : ℚ)) :
    (1 / (Fintype.card B : ℚ)) * (∑ b : B, if bad b then (1 : ℚ) else 0) ≤ δ := by
  have hc : (∑ b : B, if bad b then (1 : ℚ) else 0) =
      ((univ.filter fun b => bad b = true).card : ℚ) := by
    rw [← sum_filter]
    simp
  rw [hc]
  have hpos : (0 : ℚ) < Fintype.card B := Nat.cast_pos.mpr Fintype.card_pos
  simpa [div_eq_mul_inv, mul_comm] using (div_le_iff₀ hpos).mpr hcount

/-- An arbitrary bank-dependent invocation decision can only shrink the bad
set.  Thus adaptive designation needs no separate independence assumption. -/
lemma designated_count_bound (bad invoke : B → Bool) (δ : ℚ)
    (hcount : ((univ.filter fun b => bad b = true).card : ℚ) ≤
      δ * (Fintype.card B : ℚ)) :
    ((univ.filter fun b => (invoke b && bad b) = true).card : ℚ) ≤
      δ * (Fintype.card B : ℚ) := by
  apply le_trans _ hcount
  apply Nat.cast_le.mpr
  apply card_le_card
  intro b hb
  simp only [mem_filter, mem_univ, true_and, Bool.and_eq_true] at *
  exact hb.2

/-- The local premise is conditional on every possible incoming history. -/
def LocalBounds (δ : ℚ) (epochs : List (Epoch H B)) : Prop :=
  ∀ e ∈ epochs, ∀ h, ((univ.filter fun b => e.bad h b = true).card : ℚ) ≤
    δ * (Fintype.card B : ℚ)

/-- Fresh conditional bounds compose across arbitrary history transitions. -/
theorem anyBad_probability_le (epochs : List (Epoch H B)) (δ : ℚ)
    (hlocal : LocalBounds δ epochs) (h : H) :
    sampleProbability epochs.length (anyBad epochs h) ≤ (epochs.length : ℚ) * δ := by
  induction epochs generalizing h with
  | nil => simp [sampleProbability, anyBad]
  | cons e es ih =>
      have hrest : LocalBounds δ es := fun e' he' => hlocal e' (by simp [he'])
      rw [anyBad_probability_cons]
      have hpoint (b : B) :
          (if e.bad h b then 1 else sampleProbability es.length (anyBad es (e.next h b))) ≤
          (if e.bad h b then (1 : ℚ) else 0) + (es.length : ℚ) * δ := by
        have hi := ih hrest (e.next h b)
        by_cases hb : e.bad h b = true
        · simp only [hb, if_true]
          have hn := (sampleProbability_nonneg es.length (anyBad es (e.next h b))).trans hi
          exact le_add_of_nonneg_right hn
        · simpa [hb] using hi
      calc
        _ ≤ (1 / (Fintype.card B : ℚ)) *
            ∑ b : B, ((if e.bad h b then (1 : ℚ) else 0) + (es.length : ℚ) * δ) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun b _ => hpoint b)
            (div_nonneg zero_le_one (Nat.cast_nonneg _))
        _ = (1 / (Fintype.card B : ℚ)) *
            (∑ b : B, if e.bad h b then (1 : ℚ) else 0) + (es.length : ℚ) * δ := by
          rw [sum_add_distrib, mul_add]
          congr 1
          simp [nsmul_eq_mul, ← mul_assoc,
            Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos (α := B)))]
        _ ≤ δ + (es.length : ℚ) * δ :=
          add_le_add_right (local_count_to_probability (e.bad h) δ (hlocal e (by simp) h)) _
        _ = ((e :: es).length : ℚ) * δ := by
          simp [Nat.cast_add, add_mul, add_comm]

variable [Fintype H]

/-- Mixture over an arbitrary incoming history distribution. -/
noncomputable def runProbability (weights : H → ℚ) (epochs : List (Epoch H B))
    (event : H → Samples B epochs.length → Bool) : ℚ :=
  ∑ h, weights h * sampleProbability epochs.length (event h)

/-- Union bound for an arbitrary normalized incoming distribution, derived
from conditional fresh-bank cardinal bounds rather than unconditional bounds. -/
theorem anyBad_mixture_le (weights : H → ℚ)
    (hw : ∀ h, 0 ≤ weights h) (hnorm : ∑ h, weights h = 1)
    (epochs : List (Epoch H B)) (δ : ℚ) (hlocal : LocalBounds δ epochs) :
    runProbability weights epochs (anyBad epochs) ≤ (epochs.length : ℚ) * δ := by
  unfold runProbability
  calc
    _ ≤ ∑ h, weights h * ((epochs.length : ℚ) * δ) :=
      sum_le_sum fun h _ => mul_le_mul_of_nonneg_left
        (anyBad_probability_le epochs δ hlocal h) (hw h)
    _ = _ := by rw [← sum_mul, hnorm, one_mul]

/-- An epoch may be selected using the entire realized run, including future
banks.  Its designated bad event is a subset of the any-epoch event. -/
theorem selected_epoch_mixture_le (weights : H → ℚ)
    (hw : ∀ h, 0 ≤ weights h) (hnorm : ∑ h, weights h = 1)
    (epochs : List (Epoch H B)) (δ : ℚ) (hlocal : LocalBounds δ epochs)
    (select : H → Samples B epochs.length → ℕ) :
    runProbability weights epochs
      (fun h draws => badAt epochs h draws (select h draws)) ≤
        (epochs.length : ℚ) * δ := by
  calc
    _ ≤ runProbability weights epochs (anyBad epochs) := by
      apply sum_le_sum
      intro h hh
      apply mul_le_mul_of_nonneg_left _ (hw h)
      apply sampleProbability_mono
      intro draws hd
      exact badAt_implies_any epochs h draws (select h draws) hd
    _ ≤ _ := anyBad_mixture_le weights hw hnorm epochs δ hlocal

#print axioms sampleWeight_sum
#print axioms designated_count_bound
#print axioms anyBad_probability_le
#print axioms anyBad_mixture_le
#print axioms selected_epoch_mixture_le
end ProgressivePool.EpochComposition
