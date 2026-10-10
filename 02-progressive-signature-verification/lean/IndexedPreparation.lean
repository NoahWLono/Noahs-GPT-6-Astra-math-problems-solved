import IncrementalPreparation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! Constant-space indexed preparation.  The executable step stores only the
accumulator, counters, and a cursor.  The task list below is a proof specification
only and is never read by the cursor implementation.  Integer decoding work is
recorded separately from field multiplication work; no CPU-time claim is made. -/
namespace ProgressivePool.IndexedPreparation
open Finset Classical
open IncrementalPreparation

/-- Mixed-radix decoding: first divide by the input dimension, then the column
dimension.  This is a finite equivalence, so every task is visited exactly once. -/
def taskEquiv (s m n : ℕ) : Fin (s * m * n) ≃ Task (Fin s) (Fin n) (Fin m) :=
  (finProdFinEquiv.symm).trans
    (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl (Fin n)))

def taskAt (s m n : ℕ) (k : Fin (s * m * n)) : Task (Fin s) (Fin n) (Fin m) :=
  taskEquiv s m n k

/-- Two integer divisions and two remainders decode one task, with no stored
list or matrix-sized scheduling data. -/
theorem taskAt_decode (s m n : ℕ) (k : Fin (s * m * n)) :
    ((taskAt s m n k).1.1 : ℕ) = (k.val / n) / m ∧
    ((taskAt s m n k).1.2 : ℕ) = (k.val / n) % m ∧
    ((taskAt s m n k).2 : ℕ) = k.val % n := by
  exact ⟨rfl, rfl, rfl⟩

variable {F : Type*} [Field F] {s m n : ℕ}

structure CursorState (F : Type*) (s m : ℕ) where
  buffer : State F (Fin s) (Fin m)
  cursor : ℕ
  decodedTasks : ℕ

def initialCursor : CursorState F s m := ⟨initial, 0, 0⟩

/-- Actual constant-state iterator.  No task list occurs in this definition. -/
noncomputable def cursorStep (A : Fin n → Fin m → F) (C : Fin s → Fin n → F)
    (st : CursorState F s m) : CursorState F s m :=
  if h : st.cursor < s * m * n then
    ⟨step A C (taskAt s m n ⟨st.cursor, h⟩) st.buffer,
      st.cursor + 1, st.decodedTasks + 1⟩
  else st

noncomputable def runCursor (A : Fin n → Fin m → F) (C : Fin s → Fin n → F) :
    ℕ → CursorState F s m → CursorState F s m
  | 0, st => st
  | k + 1, st => cursorStep A C (runCursor A C k st)

/-- Specification only; this list is absent from `cursorStep` and `runCursor`. -/
def specificationTasks (s m n : ℕ) := List.ofFn (taskAt s m n)

/-- Every prefix of the constant-state iterator is the exact task fold. -/
theorem cursor_refines_fold (A : Fin n → Fin m → F) (C : Fin s → Fin n → F)
    (k : ℕ) (hk : k ≤ s * m * n) :
    runCursor A C k initialCursor =
      ⟨runTasks A C ((specificationTasks s m n).take k) initial, k, k⟩ := by
  induction k with
  | zero => simp [runCursor, initialCursor, runTasks]
  | succ k ih =>
      have hlt : k < s * m * n := Nat.lt_of_succ_le hk
      have hle : k ≤ s * m * n := hlt.le
      have hlen : k < (specificationTasks s m n).length := by
        simpa [specificationTasks] using hlt
      rw [runCursor, ih hle]
      rw [List.take_succ_eq_append_getElem hlen, runTasks_append]
      simp [cursorStep, hlt, specificationTasks, runTasks]

/-- The indexed specification computes the same stored coefficients as the
finite complete-task fold.  Bijectivity is proved by the mixed-radix equivalence. -/
theorem indexed_fold_storedRow (A : Fin n → Fin m → F) (C : Fin s → Fin n → F)
    (j : Fin s) (col : Fin m) :
    (runTasks A C (specificationTasks s m n) initial).value (j, col) =
      storedRow A (C j) col := by
  rw [runTasks_value]
  simp only [initial, zero_add, specificationTasks, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, taskAt]
  trans ∑ task : Task (Fin s) (Fin n) (Fin m),
    if task.1 = (j,col) then C task.1.1 task.2 * A task.2 task.1.2 else 0
  · apply Fintype.sum_equiv (taskEquiv s m n)
    intro k
    simp
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp [storedRow]

/-- Constant-state preparation completes the actual matrix with exactly B
field multiplications and B decoding operations. -/
theorem cursor_complete (A : Fin n → Fin m → F) (C : Fin s → Fin n → F) :
    (∀ j col, (runCursor A C (s*m*n) initialCursor).buffer.value (j,col) =
      storedRow A (C j) col) ∧
    (runCursor A C (s*m*n) initialCursor).buffer.multiplications = s*m*n ∧
    (runCursor A C (s*m*n) initialCursor).cursor = s*m*n ∧
    (runCursor A C (s*m*n) initialCursor).decodedTasks = s*m*n := by
  rw [cursor_refines_fold A C (s*m*n) (le_refl _)]
  have ht : (specificationTasks s m n).take (s*m*n) = specificationTasks s m n := by
    simpa [specificationTasks] using List.take_length (specificationTasks s m n)
  rw [ht]
  refine ⟨indexed_fold_storedRow A C, ?_, rfl, rfl⟩
  simp [runTasks_multiplications, initial, specificationTasks]

/-- Pausing the iterator retains only its current state and resumes exactly. -/
theorem runCursor_add (A : Fin n → Fin m → F) (C : Fin s → Fin n → F)
    (a b : ℕ) (st : CursorState F s m) :
    runCursor A C (a+b) st = runCursor A C b (runCursor A C a st) := by
  induction b with
  | zero => simp [runCursor]
  | succ b ih => simpa [Nat.add_succ, runCursor] using congrArg (cursorStep A C) ih

/-- One invocation advances at most W products, retaining the cursor state. -/
noncomputable def runInvocations (A : Fin n → Fin m → F) (C : Fin s → Fin n → F)
    (W : ℕ) : ℕ → CursorState F s m → CursorState F s m
  | 0, st => st
  | calls + 1, st => runCursor A C W (runInvocations A C W calls st)

theorem runInvocations_eq (A : Fin n → Fin m → F) (C : Fin s → Fin n → F)
    (W calls : ℕ) (st : CursorState F s m) :
    runInvocations A C W calls st = runCursor A C (calls * W) st := by
  induction calls with
  | zero => simp [runInvocations, runCursor]
  | succ calls ih =>
      rw [runInvocations, ih, ← runCursor_add]
      congr 1
      ring

/-- R calls each advancing W tasks complete the same constant-state iterator;
this ties the implementation directly to the scheduled work identity. -/
theorem cursor_complete_at_R (A : Fin n → Fin m → F) (C : Fin s → Fin n → F)
    (R W : ℕ) (hB : s*m*n = R*W) :
    (∀ j col, (runCursor A C (R*W) initialCursor).buffer.value (j,col) =
      storedRow A (C j) col) ∧
    (runCursor A C (R*W) initialCursor).buffer.multiplications = R*W := by
  rw [← hB]
  exact ⟨(cursor_complete A C).1, (cursor_complete A C).2.1⟩

/-- The operational cursor's products equal the ledger charge after each
complete phase, including phases whose verification depths are zero. -/
theorem cursor_ledger_matches (A : Fin n → Fin m → F) (C : Fin s → Fin n → F)
    (R W d : ℕ) (depths : List ℕ) (ledger : CostAndConfidence.CostState)
    (hR : depths.length = R) (hB : s*m*n = R*W) :
    (CostAndConfidence.runSchedule W d depths ledger).preparation =
      ledger.preparation +
        (runInvocations A C W R initialCursor).buffer.multiplications := by
  rw [(CostAndConfidence.runSchedule_increments W d depths ledger).2.1, hR,
    runInvocations_eq, (cursor_complete_at_R A C R W hB).2]

#print axioms taskAt_decode
#print axioms cursor_refines_fold
#print axioms indexed_fold_storedRow
#print axioms cursor_complete
#print axioms runCursor_add
#print axioms cursor_complete_at_R
#print axioms runInvocations_eq
#print axioms cursor_ledger_matches
end ProgressivePool.IndexedPreparation
