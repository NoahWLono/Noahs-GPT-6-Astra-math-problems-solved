import BufferedExecution

namespace ProgressivePool
open Classical
variable {F I J M H Z : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype M]

theorem runBits_length_le (current : J → I → F) (tree : QueryTree J (I → F) H) :
    (runBits rowTest current tree).length ≤ queryHeight tree := by
  induction tree with
  | leaf _ => simp [runBits,queryHeight]
  | query j w next ih =>
    simp only [runBits,List.length_cons,queryHeight]
    have hb := ih (rowTest (current j) w)
    have hm : queryHeight (next (rowTest (current j) w)) ≤
        max (queryHeight (next false)) (queryHeight (next true)) := by
      cases rowTest (current j) w <;> simp
    omega

theorem invocationDepths_length_le (current : J → I → F) {r : ℕ}
    (p : InvocationProgram J (I → F) H Z r) : (invocationDepths current p).length ≤ r := by
  induction p with
  | stop _ => simp [invocationDepths]
  | invoke batch next ih =>
    simpa [invocationDepths] using Nat.succ_le_succ (ih (runOutput current batch))

theorem invocationDepths_sum_le (current : J → I → F) {r k : ℕ}
    (p : InvocationProgram J (I → F) H Z r) (hc : invocationCaps k p) :
    (invocationDepths current p).sum ≤ (invocationDepths current p).length*k := by
  induction p with
  | stop _ => simp [invocationDepths]
  | invoke batch next ih =>
    have hb := (runBits_length_le current batch).trans hc.1
    have hn := ih (runOutput current batch) (hc.2 _)
    simp only [invocationDepths,List.sum_cons,List.length_cons]
    calc
      _ ≤ k + (invocationDepths current (next (runOutput current batch))).length*k :=
        Nat.add_le_add hb hn
      _ = _ := by simp [Nat.add_mul,Nat.add_comm]

/-- Partial phases execute exactly their charged products, not only full epochs.
There is no hidden recomputation of already-completed preparation tasks. -/
theorem buffered_prefix_work (A : I → M → F) (current future : J → I → F)
    (R W : ℕ) (p : InvocationProgram J (I → F) H Z R)
    (hB : Fintype.card J * Fintype.card M * Fintype.card I = R*W) :
    (bufferedRun A current future W p
      (IncrementalPreparation.allTasks,IncrementalPreparation.initial)).2.2.multiplications =
        (invocationDepths current p).length*W := by
  rw [buffered_preparation,IncrementalPreparation.runChunks_eq_prefix,
    IncrementalPreparation.runTasks_multiplications]
  simp only [IncrementalPreparation.initial,zero_add,List.length_take,
    IncrementalPreparation.allTasks_length,hB]
  exact min_eq_left (Nat.mul_le_mul_right W (invocationDepths_length_le current p))

/-- Actual preparation semantics and checking depths refine the charged ledger
for every reachable invocation prefix, with the initial buffer cost included. -/
theorem operational_prefix_cost (A : I → M → F) (current future : J → I → F)
    (R W d : ℕ) (p : InvocationProgram J (I → F) H Z R)
    (hB : Fintype.card J * Fintype.card M * Fintype.card I = R*W) :
    (R*W) +
      (bufferedRun A current future W p
        (IncrementalPreparation.allTasks,IncrementalPreparation.initial)).2.2.multiplications +
      d*(invocationDepths current p).sum =
        (CostAndConfidence.runSchedule W d (invocationDepths current p)
          (CostAndConfidence.initial (R*W))).preparation +
        (CostAndConfidence.runSchedule W d (invocationDepths current p)
          (CostAndConfidence.initial (R*W))).checking := by
  rw [buffered_prefix_work A current future R W p hB]
  rw [(CostAndConfidence.runSchedule_increments W d _ _).2.1,
    (CostAndConfidence.runSchedule_increments W d _ _).2.2]
  simp [CostAndConfidence.initial]

#print axioms buffered_prefix_work
#print axioms operational_prefix_cost
#print axioms invocationDepths_sum_le
end ProgressivePool
