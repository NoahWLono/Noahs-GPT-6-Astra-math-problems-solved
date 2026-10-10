import OperationalCost
import IndexedPreparation

namespace ProgressivePool
open Classical
variable {F H Z : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {s n m : ℕ}

/-- Executable-state refinement: only a matrix accumulator and scalar counters
are retained for preparation. No finite task list is stored by this machine. -/
noncomputable def cursorBufferedRun (A : Fin n → Fin m → F)
    (current future : Fin s → Fin n → F) (W : ℕ) :
    {r : ℕ} → InvocationProgram (Fin s) (Fin n → F) H Z r →
    IndexedPreparation.CursorState F s m → Z × IndexedPreparation.CursorState F s m
  | _, .stop z, pending => (z,pending)
  | _, .invoke batch next, pending =>
      cursorBufferedRun A current future W (next (runOutput current batch))
        (IndexedPreparation.runCursor A future W pending)

theorem cursorBuffered_output (A : Fin n → Fin m → F)
    (current future : Fin s → Fin n → F) (W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Fin n → F) H Z r)
    (pending : IndexedPreparation.CursorState F s m) :
    (cursorBufferedRun A current future W p pending).1 = runOutput current (flattenInvocations p) := by
  induction p generalizing pending with
  | stop _ => rfl
  | invoke batch next ih => simp [cursorBufferedRun,flattenInvocations,runOutput_bind,ih]

theorem cursorBuffered_preparation (A : Fin n → Fin m → F)
    (current future : Fin s → Fin n → F) (W : ℕ) {r : ℕ}
    (p : InvocationProgram (Fin s) (Fin n → F) H Z r)
    (pending : IndexedPreparation.CursorState F s m) :
    (cursorBufferedRun A current future W p pending).2 =
      IndexedPreparation.runCursor A future ((invocationDepths current p).length*W) pending := by
  induction p generalizing pending with
  | stop _ => simp [cursorBufferedRun,invocationDepths,IndexedPreparation.runCursor]
  | invoke batch next ih =>
    simp only [cursorBufferedRun,invocationDepths,List.length_cons]
    rw [ih, ← IndexedPreparation.runCursor_add]
    congr 1
    simp [Nat.add_mul,Nat.add_comm]

/-- The next key is correct when promoted, and its paid field work is exact.
Together with cursorBuffered_output, this permits replacing hidden early
prefetch by deferred fresh-bank sampling at the epoch boundary. -/
theorem cursorBuffered_boundary (A : Fin n → Fin m → F)
    (current future : Fin s → Fin n → F) (R W : ℕ)
    (p : InvocationProgram (Fin s) (Fin n → F) H Z R)
    (hR : (invocationDepths current p).length = R) (hB : s*m*n=R*W) :
    let pending := (cursorBufferedRun A current future W p IndexedPreparation.initialCursor).2
    (∀ j col, pending.buffer.value (j,col) = storedRow A (future j) col) ∧
      pending.buffer.multiplications = R*W := by
  dsimp only
  rw [cursorBuffered_preparation,hR]
  exact IndexedPreparation.cursor_complete_at_R A future R W hB

#print axioms cursorBuffered_output
#print axioms cursorBuffered_preparation
#print axioms cursorBuffered_boundary
end ProgressivePool
