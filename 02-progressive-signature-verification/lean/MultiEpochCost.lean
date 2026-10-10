import MultiEpochExecution

/-!
# Actual arithmetic work of arbitrary multi-epoch prefixes

These equalities concern counters incremented by the stored checker and indexed
preparation iterator.  They do not postulate a per-epoch charge.  Arithmetic
accounting does not require a Full or Ready hypothesis; semantic correctness of
promotion still requires the separate hypotheses of `run_refines`.
-/
namespace ProgressivePool.MultiEpochCost
open MultiEpochExecution StoredCheckExecution IndexedPreparation EpochComposition
variable {F H : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s m n R r : ℕ}

/-- A single actual phase's checking counters are exactly its visible length. -/
lemma phase_checking (A : Fin n → Fin m → F) (W : ℕ)
    (C future : Bank F s n) (Z : Prepared F s m) {k : ℕ}
    (p : Program F H s m n k) :
    let e := storedBufferedRun A Z C future W p initialCursor
    e.multiplications = (m+n) * e.trace.length ∧
    e.additions = (m+n) * e.trace.length ∧
    e.subtractions = e.trace.length := by
  dsimp only
  rw [storedBuffered_trace_length]
  exact ⟨storedBuffered_products A Z C future W p initialCursor,
    storedBuffered_additions A Z C future W p initialCursor,
    storedBuffered_subtractions A Z C future W p initialCursor⟩

/-- Exact checking work through all actual promotions and the final partial
phase, independent of interruption patterns or prepared values. -/
theorem run_checking (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (h : H) (C : Bank F s n) (Z : Prepared F s m)
    (future : Samples (Bank F s n) (phases.length+1)) :
    let e := run A W terminal phases h C Z future
    e.checkingMultiplications = (m+n) * e.trace.length ∧
    e.checkingAdditions = (m+n) * e.trace.length ∧
    e.checkingSubtractions = e.trace.length := by
  dsimp only
  induction phases generalizing h C Z with
  | nil => exact phase_checking A W C future.1 Z (terminal h)
  | cons p ps ih =>
      let e := storedBufferedRun A Z C future.1 W (p h) initialCursor
      have he := phase_checking A W C future.1 Z (p h)
      have hr := ih e.output future.1 (fun j col => e.pending.buffer.value (j,col)) future.2
      simp only [run, List.length_append]
      rw [he.1, he.2.1, he.2.2, hr.1, hr.2.1, hr.2.2, Nat.mul_add]
      exact ⟨rfl, rfl, rfl⟩

/-- A phase with at most R reservations has not overrun its pending task bank.
The charged count is proved from cursor execution and the syntax budget. -/
lemma phase_preparation (A : Fin n → Fin m → F) (R W : ℕ)
    (C future : Bank F s n) (Z : Prepared F s m) {k : ℕ}
    (p : Program F H s m n k) (hk : k ≤ R) (hB : s*m*n = R*W) :
    let e := storedBufferedRun A Z C future W p initialCursor
    e.pending.buffer.multiplications = e.reservations * W := by
  dsimp only
  apply storedBuffered_preparation_products
  calc
    _ ≤ k * W := Nat.mul_le_mul_right W
      (storedBuffered_reservations_le A Z C future W p initialCursor)
    _ ≤ R * W := Nat.mul_le_mul_right W hk
    _ = s*m*n := hB.symm

/-- Every actual preparation product across an arbitrary phase prefix is
accounted for exactly once, including work prefetched but never used. -/
theorem run_preparation (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hr : r ≤ R) (hB : s*m*n = R*W)
    (h : H) (C : Bank F s n) (Z : Prepared F s m)
    (future : Samples (Bank F s n) (phases.length+1)) :
    (run A W terminal phases h C Z future).preparationMultiplications =
      (run A W terminal phases h C Z future).reservations * W := by
  induction phases generalizing h C Z with
  | nil => exact phase_preparation A R W C future.1 Z (terminal h) hr hB
  | cons p ps ih =>
      let e := storedBufferedRun A Z C future.1 W (p h) initialCursor
      have he := phase_preparation A R W C future.1 Z (p h) (le_refl R) hB
      have hrest := ih e.output future.1 (fun j col => e.pending.buffer.value (j,col)) future.2
      simp only [run]
      rw [he, hrest, Nat.add_mul]

/-- Cold initialization changes no checking arithmetic counters. -/
theorem coldRun_checking (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R)) (h : H)
    (draws : Samples (Bank F s n) (phases.length+2)) :
    let e := coldRun A W terminal phases h draws
    e.checkingMultiplications = (m+n) * e.trace.length ∧
    e.checkingAdditions = (m+n) * e.trace.length ∧
    e.checkingSubtractions = e.trace.length := by
  exact run_checking A W terminal phases h draws.1
    (fun j col => (runCursor A draws.1 (s*m*n) initialCursor).buffer.value (j,col)) draws.2

/-- Cold setup is computed, so arbitrary prefixes include B initialization
products as well as every executed next-buffer preparation product. -/
theorem coldRun_preparation (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hr : r ≤ R) (hB : s*m*n = R*W) (h : H)
    (draws : Samples (Bank F s n) (phases.length+2)) :
    (coldRun A W terminal phases h draws).preparationMultiplications =
      s*m*n + (coldRun A W terminal phases h draws).reservations * W := by
  simp only [coldRun]
  rw [(cursor_complete A draws.1).2.1,
    run_preparation A W terminal phases hr hB]

/-- Initialization-inclusive total of actual field multiplications, derived
from both operational counters for every finite execution prefix. -/
theorem coldRun_total_multiplications (A : Fin n → Fin m → F) (W : ℕ)
    (terminal : Phase F H s m n r) (phases : List (Phase F H s m n R))
    (hr : r ≤ R) (hB : s*m*n = R*W) (h : H)
    (draws : Samples (Bank F s n) (phases.length+2)) :
    let e := coldRun A W terminal phases h draws
    e.preparationMultiplications + e.checkingMultiplications =
      s*m*n + e.reservations * W + (m+n) * e.trace.length := by
  dsimp only
  rw [coldRun_preparation A W terminal phases hr hB,
    (coldRun_checking A W terminal phases h draws).1]

#print axioms run_checking
#print axioms run_preparation
#print axioms coldRun_checking
#print axioms coldRun_preparation
#print axioms coldRun_total_multiplications
end ProgressivePool.MultiEpochCost
