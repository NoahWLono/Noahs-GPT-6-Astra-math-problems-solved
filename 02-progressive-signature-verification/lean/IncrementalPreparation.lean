import StoredRows
import CostAndConfidence

/-! Operational preparation of the stored rows `C*A`.  A task performs exactly
one field multiplication and one accumulator addition.  Chunk execution folds
actual updates over pending tasks; pausing never recomputes earlier products. -/
namespace ProgressivePool.IncrementalPreparation
open Finset Classical
variable {F J I M : Type*} [Field F] [Fintype J] [Fintype I] [Fintype M]

abbrev Task (J I M : Type*) := (J × M) × I

/-- A complete finite enumeration, with every coefficient/input task once. -/
noncomputable def allTasks : List (Task J I M) :=
  (univ : Finset (Task J I M)).toList

/-- Stored coefficients and an instrumented field-multiplication counter. -/
structure State (F J M : Type*) where
  value : J × M → F
  multiplications : ℕ

/-- The only field multiplication in a preparation step. -/
noncomputable def step (A : I → M → F) (C : J → I → F)
    (task : Task J I M) (st : State F J M) : State F J M :=
  let product := C task.1.1 task.2 * A task.2 task.1.2
  ⟨Function.update st.value task.1 (st.value task.1 + product), st.multiplications + 1⟩

def initial : State F J M := ⟨fun _ => 0, 0⟩

/-- Concrete sequential multiply-add execution. -/
noncomputable def runTasks (A : I → M → F) (C : J → I → F) :
    List (Task J I M) → State F J M → State F J M
  | [], st => st
  | task :: tasks, st => runTasks A C tasks (step A C task st)

theorem step_multiplications (A : I → M → F) (C : J → I → F)
    (task : Task J I M) (st : State F J M) :
    (step A C task st).multiplications = st.multiplications + 1 := rfl

theorem step_designated_coefficient (A : I → M → F) (C : J → I → F)
    (task : Task J I M) (st : State F J M) :
    (step A C task st).value task.1 =
      st.value task.1 + C task.1.1 task.2 * A task.2 task.1.2 := by simp [step]

theorem step_other_coefficient (A : I → M → F) (C : J → I → F)
    (task : Task J I M) (st : State F J M) (key : J × M) (hne : key ≠ task.1) :
    (step A C task st).value key = st.value key := by simp [step, Function.update_of_ne hne]

/-- Exact no-recomputation multiplication count for any task prefix. -/
theorem runTasks_multiplications (A : I → M → F) (C : J → I → F)
    (tasks : List (Task J I M)) (st : State F J M) :
    (runTasks A C tasks st).multiplications = st.multiplications + tasks.length := by
  induction tasks generalizing st with
  | nil => simp [runTasks]
  | cons task tasks ih =>
      rw [runTasks, ih]
      simp [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Every intermediate accumulator equals precisely the contributions already
executed, proving a semantic invariant rather than only a work counter. -/
theorem runTasks_value (A : I → M → F) (C : J → I → F)
    (tasks : List (Task J I M)) (st : State F J M) (key : J × M) :
    (runTasks A C tasks st).value key = st.value key +
      (tasks.map fun task => if task.1 = key then
        C task.1.1 task.2 * A task.2 task.1.2 else 0).sum := by
  induction tasks generalizing st with
  | nil => simp [runTasks]
  | cons task tasks ih =>
      rw [runTasks, ih]
      by_cases h : key = task.1
      · simp [step, h, List.sum_cons, add_assoc]
      · simp [step, h, Ne.symm h, List.sum_cons, add_assoc]

/-- Pausing and resuming consecutive task lists is exactly uninterrupted work. -/
theorem runTasks_append (A : I → M → F) (C : J → I → F)
    (pre post : List (Task J I M)) (st : State F J M) :
    runTasks A C (pre ++ post) st = runTasks A C post (runTasks A C pre st) := by
  induction pre generalizing st with
  | nil => rfl
  | cons task pre ih => exact ih (step A C task st)

theorem allTasks_length : (allTasks (J := J) (I := I) (M := M)).length =
    Fintype.card J * Fintype.card M * Fintype.card I := by
  simp [allTasks, Fintype.card_prod]

/-- Completing the enumerated tasks computes every stored coefficient `C*A`.
The final equality is derived from the step semantics. -/
theorem complete_storedRow (A : I → M → F) (C : J → I → F) (j : J) (m : M) :
    (runTasks A C allTasks initial).value (j, m) = storedRow A (C j) m := by
  rw [runTasks_value]
  simp only [initial, zero_add, allTasks, Finset.sum_map_toList]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [storedRow]

lemma take_add_chunks {α : Type*} (a b : ℕ) (xs : List α) :
    xs.take (a + b) = xs.take a ++ (xs.drop a).take b := by
  induction a generalizing xs with
  | zero => simp
  | succ a ih => cases xs <;> simp [Nat.succ_add, ih]

/-- Each invocation consumes at most `W` still-pending tasks; finished tasks
are dropped, and the accumulator is retained for the next invocation. -/
noncomputable def runChunks (A : I → M → F) (C : J → I → F) (W : ℕ) :
    ℕ → List (Task J I M) → State F J M → State F J M
  | 0, _, st => st
  | n + 1, tasks, st => runChunks A C W n (tasks.drop W)
      (runTasks A C (tasks.take W) st)

/-- Exact correspondence between scheduled chunks and the executed prefix. -/
theorem runChunks_eq_prefix (A : I → M → F) (C : J → I → F) (W n : ℕ)
    (tasks : List (Task J I M)) (st : State F J M) :
    runChunks A C W n tasks st = runTasks A C (tasks.take (n * W)) st := by
  induction n generalizing tasks st with
  | zero => simp [runChunks, runTasks]
  | succ n ih =>
      rw [runChunks, ih, ← runTasks_append, ← take_add_chunks]
      congr 2
      ring

/-- At `R` invocations the concrete incremental matrix computation is complete,
using exactly `B=R*W` field multiplications, without hidden initialization work. -/
theorem scheduled_preparation_correct (A : I → M → F) (C : J → I → F)
    (R W : ℕ)
    (hB : Fintype.card J * Fintype.card M * Fintype.card I = R * W) :
    (∀ j m, (runChunks A C W R allTasks initial).value (j, m) = storedRow A (C j) m) ∧
    (runChunks A C W R allTasks initial).multiplications = R * W := by
  have hlen : (allTasks (J := J) (I := I) (M := M)).length = R * W :=
    allTasks_length.trans hB
  rw [runChunks_eq_prefix, ← hlen, List.take_length]
  constructor
  · exact complete_storedRow A C
  · simp [runTasks_multiplications, initial]

/-- The ledger's scheduled preparation charge matches the actual incremental
products for each complete buffer phase, for arbitrary interruption depths. -/
theorem ledger_matches_preparation (A : I → M → F) (C : J → I → F)
    (R W d : ℕ) (depths : List ℕ) (ledger : CostAndConfidence.CostState)
    (hR : depths.length = R)
    (hB : Fintype.card J * Fintype.card M * Fintype.card I = R * W) :
    (CostAndConfidence.runSchedule W d depths ledger).preparation =
      ledger.preparation + (runChunks A C W R allTasks initial).multiplications := by
  rw [(CostAndConfidence.runSchedule_increments W d depths ledger).2.1, hR,
    (scheduled_preparation_correct A C R W hB).2]

#print axioms runTasks_value
#print axioms complete_storedRow
#print axioms runChunks_eq_prefix
#print axioms scheduled_preparation_correct
#print axioms ledger_matches_preparation
end ProgressivePool.IncrementalPreparation
