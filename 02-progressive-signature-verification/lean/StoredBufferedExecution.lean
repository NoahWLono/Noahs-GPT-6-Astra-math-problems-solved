import StoredCheckExecution
import CursorBufferedExecution

/-!
# Stored checking interleaved with constant-state next-buffer preparation

Every invocation first reserves one slot and advances the hidden next-buffer
cursor by W steps, then runs its batch against the active stored matrix.  Empty
batches reserve and prepare normally.  Checking counters record actual executed
multiply-add arithmetic, not a raw-row oracle surrogate.
-/
namespace ProgressivePool.StoredBufferedExecution
open StoredCheckExecution
variable {F H Y : Type*} [Field F] [DecidableEq F]
variable {s m n : ℕ}

/-- Relabel every invocation's actual signature/target inputs by its residual. -/
def mapInvocationInputs (A : Fin n → Fin m → F) : {r : ℕ} →
    InvocationProgram (Fin s) (Input F m n) H Y r →
      InvocationProgram (Fin s) (Fin n → F) H Y r
  | _, .stop y => .stop y
  | _, .invoke batch next => .invoke
      (mapQueries (fun input => mvResidual A input.1 input.2) batch)
      (fun h => mapInvocationInputs A (next h))

structure Result (F : Type*) (s m : ℕ) (Y : Type*) where
  output : Y
  trace : List Bool
  depths : List ℕ
  pending : IndexedPreparation.CursorState F s m
  multiplications : ℕ
  additions : ℕ
  subtractions : ℕ
  reservations : ℕ

/-- All checking branches are chosen by actual stored arithmetic.  The pending
matrix is never consulted for a current-bank branch or visible output. -/
noncomputable def storedBufferedRun (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ) :
    {r : ℕ} → InvocationProgram (Fin s) (Input F m n) H Y r →
      IndexedPreparation.CursorState F s m → Result F s m Y
  | _, .stop y, pending => ⟨y, [], [], pending, 0, 0, 0, 0⟩
  | _, .invoke batch next, pending =>
      let pending' := IndexedPreparation.runCursor A future W pending
      let checked := storedRun Z current batch
      let rest := storedBufferedRun A Z current future W (next checked.output) pending'
      ⟨rest.output, checked.trace ++ rest.trace, checked.trace.length :: rest.depths,
        rest.pending, checked.multiplications + rest.multiplications,
        checked.additions + rest.additions,
        checked.subtractions + rest.subtractions, 1 + rest.reservations⟩

lemma runOutput_bind_local (current : Fin s → Fin n → F)
    (tree : QueryTree (Fin s) (Fin n → F) H)
    (next : H → QueryTree (Fin s) (Fin n → F) Y) :
    runOutput current (bindQueries tree next) = runOutput current (next (runOutput current tree)) := by
  induction tree with
  | leaf h => rfl
  | query j w branches ih => simp [bindQueries, runOutput, ih]

lemma runBits_bind (current : Fin s → Fin n → F)
    (tree : QueryTree (Fin s) (Fin n → F) H)
    (next : H → QueryTree (Fin s) (Fin n → F) Y) :
    runBits rowTest current (bindQueries tree next) =
      runBits rowTest current tree ++ runBits rowTest current (next (runOutput current tree)) := by
  induction tree with
  | leaf h => rfl
  | query j w branches ih => simp [bindQueries, runBits, runOutput, ih]

/-- The visible output is exactly the existing current-bank experiment. -/
theorem storedBuffered_output (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ)
    (hZ : ∀ j col, Z j col = storedRow A (current j) col) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : IndexedPreparation.CursorState F s m) :
    (storedBufferedRun A Z current future W p pending).output =
      runOutput current (flattenInvocations (mapInvocationInputs A p)) := by
  induction p generalizing pending with
  | stop _ => rfl
  | invoke batch next ih =>
      simp only [storedBufferedRun, mapInvocationInputs, flattenInvocations,
        runOutput_bind_local, ih, storedRun_output A Z current hZ]

/-- The full bit trace, not just the final output, matches the model. -/
theorem storedBuffered_trace (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ)
    (hZ : ∀ j col, Z j col = storedRow A (current j) col) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : IndexedPreparation.CursorState F s m) :
    (storedBufferedRun A Z current future W p pending).trace =
      runBits rowTest current (flattenInvocations (mapInvocationInputs A p)) := by
  induction p generalizing pending with
  | stop _ => rfl
  | invoke batch next ih =>
      simp only [storedBufferedRun, mapInvocationInputs, flattenInvocations,
        runBits_bind, ih, storedRun_output A Z current hZ, storedRun_trace A Z current hZ]

/-- Invocation depths are measured from the actual stored execution. -/
theorem storedBuffered_depths (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ)
    (hZ : ∀ j col, Z j col = storedRow A (current j) col) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : IndexedPreparation.CursorState F s m) :
    (storedBufferedRun A Z current future W p pending).depths =
      invocationDepths current (mapInvocationInputs A p) := by
  induction p generalizing pending with
  | stop _ => rfl
  | invoke batch next ih =>
      simp only [storedBufferedRun, mapInvocationInputs, invocationDepths, ih,
        storedRun_output A Z current hZ, storedRun_trace A Z current hZ]

/-- One reservation per invocation, including every zero-depth batch. -/
theorem storedBuffered_reservations (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : IndexedPreparation.CursorState F s m) :
    (storedBufferedRun A Z current future W p pending).reservations =
      (storedBufferedRun A Z current future W p pending).depths.length := by
  induction p generalizing pending with
  | stop _ => rfl
  | invoke batch next ih => simp [storedBufferedRun, ih, Nat.add_comm]

/-- Reservations cannot exceed the program's finite invocation budget. -/
theorem storedBuffered_reservations_le (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : IndexedPreparation.CursorState F s m) :
    (storedBufferedRun A Z current future W p pending).reservations ≤ r := by
  induction p generalizing pending with
  | stop _ => simp [storedBufferedRun]
  | invoke batch next ih =>
      simpa [storedBufferedRun, Nat.add_comm] using
        Nat.succ_le_succ (ih (storedRun Z current batch).output
          (IndexedPreparation.runCursor A future W pending))

/-- Actual checking products equal d times the sum of measured batch depths. -/
theorem storedBuffered_products (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : IndexedPreparation.CursorState F s m) :
    (storedBufferedRun A Z current future W p pending).multiplications =
      (m+n) * (storedBufferedRun A Z current future W p pending).depths.sum := by
  induction p generalizing pending with
  | stop _ => simp [storedBufferedRun]
  | invoke batch next ih =>
      simp only [storedBufferedRun, List.sum_cons]
      rw [ih, (storedRun_work Z current batch).1, Nat.mul_add]

/-- Exact addition count; subtraction is counted separately. -/
theorem storedBuffered_additions (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : IndexedPreparation.CursorState F s m) :
    (storedBufferedRun A Z current future W p pending).additions =
      (m+n) * (storedBufferedRun A Z current future W p pending).depths.sum := by
  induction p generalizing pending with
  | stop _ => simp [storedBufferedRun]
  | invoke batch next ih =>
      simp only [storedBufferedRun, List.sum_cons]
      rw [ih, (storedRun_work Z current batch).2.1, Nat.mul_add]

theorem storedBuffered_subtractions (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : IndexedPreparation.CursorState F s m) :
    (storedBufferedRun A Z current future W p pending).subtractions =
      (storedBufferedRun A Z current future W p pending).depths.sum := by
  induction p generalizing pending with
  | stop _ => rfl
  | invoke batch next ih =>
      simp only [storedBufferedRun, List.sum_cons]
      rw [ih, (storedRun_work Z current batch).2.2]

theorem storedBuffered_trace_length (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : IndexedPreparation.CursorState F s m) :
    (storedBufferedRun A Z current future W p pending).trace.length =
      (storedBufferedRun A Z current future W p pending).depths.sum := by
  induction p generalizing pending with
  | stop _ => rfl
  | invoke batch next ih => simp [storedBufferedRun, ih]

/-- Hidden next-buffer state advances by W steps per actual reservation,
without inspecting the current invocation's stopping depth. -/
theorem storedBuffered_preparation (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (pending : IndexedPreparation.CursorState F s m) :
    (storedBufferedRun A Z current future W p pending).pending =
      IndexedPreparation.runCursor A future
        ((storedBufferedRun A Z current future W p pending).depths.length * W) pending := by
  induction p generalizing pending with
  | stop _ => simp [storedBufferedRun, IndexedPreparation.runCursor]
  | invoke batch next ih =>
      simp only [storedBufferedRun, List.length_cons]
      rw [ih, ← IndexedPreparation.runCursor_add]
      congr 1
      simp [Nat.add_mul, Nat.add_comm]

/-- Every partial phase executes precisely its charged preparation products,
provided the reservation prefix fits in the pending buffer's task budget. -/
theorem storedBuffered_preparation_products (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (hcap : (storedBufferedRun A Z current future W p IndexedPreparation.initialCursor).reservations * W
      ≤ s*m*n) :
    (storedBufferedRun A Z current future W p IndexedPreparation.initialCursor).pending.buffer.multiplications =
      (storedBufferedRun A Z current future W p IndexedPreparation.initialCursor).reservations * W := by
  rw [storedBuffered_reservations] at hcap ⊢
  rw [storedBuffered_preparation, IndexedPreparation.cursor_refines_fold A future _ hcap]
  simp only [IncrementalPreparation.runTasks_multiplications, IncrementalPreparation.initial,
    Nat.zero_add, List.length_take, IndexedPreparation.specificationTasks, List.length_ofFn]
  exact Nat.min_eq_left hcap

/-- At a full reservation boundary the next matrix is correct for promotion.
This theorem concerns the actual interleaved stored-check/cursor execution. -/
theorem storedBuffered_boundary (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (R W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Input F m n) H Y r)
    (hR : (storedBufferedRun A Z current future W p IndexedPreparation.initialCursor).reservations = R)
    (hB : s*m*n = R*W) :
    let pending := (storedBufferedRun A Z current future W p IndexedPreparation.initialCursor).pending
    (∀ j col, pending.buffer.value (j,col) = storedRow A (future j) col) ∧
      pending.buffer.multiplications = R*W := by
  dsimp only
  rw [storedBuffered_reservations] at hR
  rw [storedBuffered_preparation, hR]
  exact IndexedPreparation.cursor_complete_at_R A future R W hB

#print axioms storedBuffered_output
#print axioms storedBuffered_trace
#print axioms storedBuffered_products
#print axioms storedBuffered_reservations
#print axioms storedBuffered_preparation
#print axioms storedBuffered_boundary
#print axioms storedBuffered_preparation_products
#print axioms storedBuffered_reservations_le
end ProgressivePool.StoredBufferedExecution

namespace ProgressivePool
export StoredBufferedExecution
  (mapInvocationInputs storedBufferedRun storedBuffered_output storedBuffered_trace
   storedBuffered_depths storedBuffered_reservations storedBuffered_reservations_le
   storedBuffered_products storedBuffered_additions storedBuffered_subtractions
   storedBuffered_trace_length storedBuffered_preparation storedBuffered_preparation_products
   storedBuffered_boundary)
end ProgressivePool
