import StoredBufferedExecution
import FreshSampling

/-!
# The reserved final invocation, with fresh uniform indices

The candidate `(sigma,target)`, active stored matrix, and threshold `t` are fixed
parameters before the fresh function `Fin t → Fin s` is supplied.  Every one of
the requested checks is executed; rejection does not short-circuit arithmetic.
The invocation advances next-buffer preparation and consumes one reservation
even at threshold zero.
-/
namespace ProgressivePool.FinalStoredInvocation
open Finset Classical StoredCheckExecution IndexedPreparation
variable {F : Type*} [Field F] [DecidableEq F]
variable {s m n : ℕ}

structure CheckResult where
  accepted : Bool
  multiplications : ℕ
  additions : ℕ
  subtractions : ℕ

/-- All requested stored checks execute, and their computed bits are ANDed. -/
def checkFresh (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (input : Input F m n) : (t : ℕ) → (Fin t → Fin s) → CheckResult
  | 0, _ => ⟨true, 0, 0, 0⟩
  | t + 1, draws =>
      let checked := evalStored Z C (draws 0) input
      let rest := checkFresh Z C input t (fun i => draws i.succ)
      ⟨decide (checked.value = 0) && rest.accepted,
        checked.multiplications + rest.multiplications,
        checked.additions + rest.additions,
        checked.subtractions + rest.subtractions⟩

theorem checkFresh_accepted (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (input : Input F m n) (t : ℕ) (draws : Fin t → Fin s) :
    (checkFresh Z C input t draws).accepted = true ↔
      ∀ i, (evalStored Z C (draws i) input).value = 0 := by
  induction t with
  | zero => simp [checkFresh]
  | succ t ih =>
      simp only [checkFresh, Bool.and_eq_true, decide_eq_true_eq, ih, Fin.forall_fin_succ]

/-- Exact final-call checking work, including at t=0. -/
theorem checkFresh_work (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (input : Input F m n) (t : ℕ) (draws : Fin t → Fin s) :
    (checkFresh Z C input t draws).multiplications = (m+n)*t ∧
    (checkFresh Z C input t draws).additions = (m+n)*t ∧
    (checkFresh Z C input t draws).subtractions = t := by
  induction t with
  | zero => simp [checkFresh]
  | succ t ih =>
      have h := ih (fun i => draws i.succ)
      simp only [checkFresh, evalStored_multiplications, evalStored_additions,
        evalStored_subtractions]
      rw [h.1, h.2.1, h.2.2]
      simp [Nat.mul_succ, Nat.add_comm]

/-- The zero set is defined from the actual stored arithmetic. -/
noncomputable def zeroRows (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (input : Input F m n) : Finset (Fin s) :=
  univ.filter fun j => (evalStored Z C j input).value = 0

theorem zeroRows_eq_residual (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (hZ : ∀ j col, Z j col = storedRow A (C j) col) (input : Input F m n) :
    zeroRows Z C input =
      univ.filter (fun j => rowDot (mvResidual A input.1 input.2) (C j) = 0) := by
  ext j
  simp only [zeroRows, mem_filter, mem_univ, true_and,
    stored_value_correct A Z C hZ]

theorem checkFresh_accepted_iff_mem (Z : Fin s → Fin m → F)
    (C : Fin s → Fin n → F) (input : Input F m n) (t : ℕ) (draws : Fin t → Fin s) :
    (checkFresh Z C input t draws).accepted = true ↔ ∀ i, draws i ∈ zeroRows Z C input := by
  simpa only [zeroRows, mem_filter, mem_univ, true_and] using
    checkFresh_accepted Z C input t draws

/-- Actual accepting fresh strings equal the explicit independent-sampling
all-hit event.  Nothing about the candidate or t depends on these draws. -/
theorem checkFresh_accepting_set (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (input : Input F m n) (t : ℕ) :
    (univ.filter fun draws : Fin t → Fin s => (checkFresh Z C input t draws).accepted = true) =
      FreshSampling.allHit (zeroRows Z C input) t := by
  ext draws
  simp only [mem_filter, mem_univ, true_and, FreshSampling.allHit,
    checkFresh_accepted_iff_mem]

/-- Exact acceptance probability from the actual checker on a uniform fresh
function.  Together with a prior-state mixture, this supplies the required
conditional fresh-indices interpretation. -/
theorem checkFresh_uniform_probability (Z : Fin s → Fin m → F)
    (C : Fin s → Fin n → F) (input : Input F m n) (t : ℕ) :
    (((univ.filter fun draws : Fin t → Fin s =>
      (checkFresh Z C input t draws).accepted = true).card : ℚ) /
        (univ : Finset (Fin t → Fin s)).card) =
      FreshSampling.acceptProbability (zeroRows Z C input) t := by
  rw [checkFresh_accepting_set]
  rfl

theorem checkFresh_uniform_probability_power (Z : Fin s → Fin m → F)
    (C : Fin s → Fin n → F) (input : Input F m n) (t : ℕ) :
    (((univ.filter fun draws : Fin t → Fin s =>
      (checkFresh Z C input t draws).accepted = true).card : ℚ) /
        (univ : Finset (Fin t → Fin s)).card) =
      (((zeroRows Z C input).card : ℚ) / (s : ℚ)) ^ t := by
  rw [checkFresh_uniform_probability, FreshSampling.acceptProbability_eq]

structure InvocationResult (F : Type*) (s m : ℕ) where
  accepted : Bool
  pending : CursorState F s m
  reservations : ℕ
  multiplications : ℕ
  additions : ℕ
  subtractions : ℕ

/-- Reserve and prepare before the final actual stored checks.  Work counters
here are the final call's checking work; reservations start from the supplied
prior count, and the pending cursor retains all earlier preparation work. -/
noncomputable def runFinalInvocation (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W prior : ℕ)
    (pending : CursorState F s m) (input : Input F m n)
    (t : ℕ) (draws : Fin t → Fin s) : InvocationResult F s m :=
  let pending' := runCursor A future W pending
  let checked := checkFresh Z current input t draws
  ⟨checked.accepted, pending', prior+1, checked.multiplications,
    checked.additions, checked.subtractions⟩

theorem final_invocation_counters (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W prior : ℕ)
    (pending : CursorState F s m) (input : Input F m n) (t : ℕ) (draws : Fin t → Fin s) :
    let e := runFinalInvocation A Z current future W prior pending input t draws
    e.reservations = prior+1 ∧ e.multiplications = (m+n)*t ∧
      e.additions = (m+n)*t ∧ e.subtractions = t := by
  exact ⟨rfl, checkFresh_work Z current input t draws⟩

theorem final_invocation_acceptance (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W prior : ℕ)
    (pending : CursorState F s m) (input : Input F m n) (t : ℕ) (draws : Fin t → Fin s) :
    (runFinalInvocation A Z current future W prior pending input t draws).accepted = true ↔
      ∀ i, draws i ∈ zeroRows Z current input :=
  checkFresh_accepted_iff_mem Z current input t draws

lemma cursor_prefix_products (A : Fin n → Fin m → F) (C : Fin s → Fin n → F)
    (k : ℕ) (hk : k ≤ s*m*n) :
    (runCursor A C k initialCursor).buffer.multiplications = k := by
  rw [cursor_refines_fold A C k hk]
  simp only [IncrementalPreparation.runTasks_multiplications, IncrementalPreparation.initial,
    Nat.zero_add, List.length_take, specificationTasks, List.length_ofFn]
  exact Nat.min_eq_left hk

/-- If the last partial phase has room for the reserved final call, advancing
its actual cursor performs exactly W additional field multiplications. -/
theorem final_invocation_preparation (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F)
    (R W prior : ℕ) (pending : CursorState F s m)
    (hcursor : pending = runCursor A future (prior*W) initialCursor)
    (hcap : prior+1 ≤ R) (hB : s*m*n = R*W)
    (input : Input F m n) (t : ℕ) (draws : Fin t → Fin s) :
    let e := runFinalInvocation A Z current future W prior pending input t draws
    e.pending = runCursor A future ((prior+1)*W) initialCursor ∧
    e.pending.buffer.multiplications = pending.buffer.multiplications + W := by
  have hafter : (prior+1)*W ≤ s*m*n := by
    rw [hB]
    exact Nat.mul_le_mul_right W hcap
  have hbefore : prior*W ≤ s*m*n :=
    (Nat.mul_le_mul_right W (Nat.le_succ prior)).trans hafter
  have hstep : runCursor A future W pending =
      runCursor A future ((prior+1)*W) initialCursor := by
    rw [hcursor, ← runCursor_add]
    congr 1
    simp [Nat.add_mul]
  dsimp only [runFinalInvocation]
  constructor
  · exact hstep
  · rw [hstep, hcursor, cursor_prefix_products A future _ hafter,
      cursor_prefix_products A future _ hbefore]
    simp [Nat.add_mul]

/-- Threshold zero still reserves and prepares; only checking work is zero. -/
theorem zero_threshold_reserved (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (current future : Fin s → Fin n → F) (W prior : ℕ)
    (pending : CursorState F s m) (input : Input F m n) (draws : Fin 0 → Fin s) :
    let e := runFinalInvocation A Z current future W prior pending input 0 draws
    e.accepted = true ∧ e.reservations = prior+1 ∧
      e.pending = runCursor A future W pending ∧ e.multiplications = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms checkFresh_accepted
#print axioms checkFresh_work
#print axioms checkFresh_uniform_probability
#print axioms checkFresh_uniform_probability_power
#print axioms final_invocation_counters
#print axioms final_invocation_preparation
#print axioms zero_threshold_reserved
end ProgressivePool.FinalStoredInvocation
