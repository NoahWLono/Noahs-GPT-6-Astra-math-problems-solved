import InvocationBudget
import IncrementalPreparation

namespace ProgressivePool
open Classical
variable {F I J M H Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype M]

abbrev PendingBuffer (F J I M : Type*) :=
  List (IncrementalPreparation.Task J I M) × IncrementalPreparation.State F J M

noncomputable def advanceBuffer (A : I → M → F) (future : J → I → F) (W : ℕ)
    (pending : PendingBuffer F J I M) : PendingBuffer F J I M :=
  (pending.1.drop W,
    IncrementalPreparation.runTasks A future (pending.1.take W) pending.2)

/-- One reservation and one preparation chunk precede each invocation, even
when its check tree is empty. No future-bank value affects the visible result. -/
noncomputable def bufferedRun (A : I → M → F) (current future : J → I → F) (W : ℕ) :
    {r : ℕ} → InvocationProgram J (I → F) H Z r → PendingBuffer F J I M →
      Z × PendingBuffer F J I M
  | _, .stop z, pending => (z,pending)
  | _, .invoke batch next, pending =>
      bufferedRun A current future W (next (runOutput current batch))
        (advanceBuffer A future W pending)

def invocationDepths (current : J → I → F) :
    {r : ℕ} → InvocationProgram J (I → F) H Z r → List ℕ
  | _, .stop _ => []
  | _, .invoke batch next => (runBits rowTest current batch).length ::
      invocationDepths current (next (runOutput current batch))

theorem runOutput_bind (current : J → I → F) (tree : QueryTree J (I → F) H)
    (next : H → QueryTree J (I → F) Z) :
    runOutput current (bindQueries tree next) = runOutput current (next (runOutput current tree)) := by
  induction tree with
  | leaf _ => rfl
  | query j w branches ih => simp [bindQueries,runOutput,ih]

/-- Observational projection: fixing the current bank, the entire epoch output
is independent of prefetched next-bank values and intermediate accumulators. -/
theorem buffered_output_projection (A : I → M → F) (current future : J → I → F)
    (W : ℕ) {r : ℕ} (p : InvocationProgram J (I → F) H Z r)
    (pending : PendingBuffer F J I M) :
    (bufferedRun A current future W p pending).1 = runOutput current (flattenInvocations p) := by
  induction p generalizing pending with
  | stop z => rfl
  | invoke batch next ih =>
    simp [bufferedRun,flattenInvocations,runOutput_bind,ih]

/-- The hidden preparation state advances once per reserved invocation,
independently of whether the check depth is zero or positive. -/
theorem buffered_preparation (A : I → M → F) (current future : J → I → F)
    (W : ℕ) {r : ℕ} (p : InvocationProgram J (I → F) H Z r)
    (pending : PendingBuffer F J I M) :
    (bufferedRun A current future W p pending).2.2 =
      IncrementalPreparation.runChunks A future W (invocationDepths current p).length
        pending.1 pending.2 := by
  induction p generalizing pending with
  | stop z => rfl
  | invoke batch next ih =>
    simp only [bufferedRun,invocationDepths,List.length_cons,IncrementalPreparation.runChunks]
    exact ih _ (advanceBuffer A future W pending)

/-- Concrete boundary refinement: after R reserved calls the next stored matrix
is correct and exactly R*W field products have been executed. -/
theorem buffered_boundary_correct (A : I → M → F) (current future : J → I → F)
    (R W : ℕ) {r : ℕ} (p : InvocationProgram J (I → F) H Z r)
    (hR : (invocationDepths current p).length = R)
    (hB : Fintype.card J * Fintype.card M * Fintype.card I = R*W) :
    let result := bufferedRun A current future W p
      (IncrementalPreparation.allTasks,IncrementalPreparation.initial)
    (∀ j m, result.2.2.value (j,m) = storedRow A (future j) m) ∧
      result.2.2.multiplications = R*W := by
  dsimp only
  rw [buffered_preparation,hR]
  exact IncrementalPreparation.scheduled_preparation_correct A future R W hB

#print axioms buffered_output_projection
#print axioms buffered_boundary_correct
end ProgressivePool
