import StoredRows
import FinalResidual
import Mathlib.Algebra.BigOperators.Fin

/-!
# Executing checks against the active prepared matrix

The operational checker reads only prepared `Z`, private `C`, and the input
`(sigma,target)`.  The public matrix `A` occurs in refinement theorems, never in
the checker.  Dot products are explicit multiply-add recursions.  Additions and
the final subtraction are counted separately; integer/control work is excluded.
-/
namespace ProgressivePool.StoredCheckExecution
open Finset

variable {F : Type*} [Field F]

structure ArithmeticResult (F : Type*) where
  value : F
  multiplications : ℕ
  additions : ℕ
  subtractions : ℕ

/-- A zero-initialized dot product: one product and one addition per entry. -/
def dotLoop : (d : ℕ) → (Fin d → F) → (Fin d → F) → ArithmeticResult F
  | 0, _, _ => ⟨0, 0, 0, 0⟩
  | d + 1, x, y =>
      let rest := dotLoop d (fun i => x i.succ) (fun i => y i.succ)
      let product := x 0 * y 0
      ⟨product + rest.value, rest.multiplications + 1,
        rest.additions + 1, rest.subtractions⟩

@[simp] theorem dotLoop_value (d : ℕ) (x y : Fin d → F) :
    (dotLoop d x y).value = ∑ i, x i * y i := by
  induction d with
  | zero => simp [dotLoop]
  | succ d ih => simp [dotLoop, ih, Fin.sum_univ_succ]

@[simp] theorem dotLoop_multiplications (d : ℕ) (x y : Fin d → F) :
    (dotLoop d x y).multiplications = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [dotLoop, ih]

@[simp] theorem dotLoop_additions (d : ℕ) (x y : Fin d → F) :
    (dotLoop d x y).additions = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [dotLoop, ih]

@[simp] theorem dotLoop_subtractions (d : ℕ) (x y : Fin d → F) :
    (dotLoop d x y).subtractions = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [dotLoop, ih]

abbrev Input (F : Type*) (m n : ℕ) := (Fin m → F) × (Fin n → F)

variable {s m n : ℕ}

/-- Actual stored-row arithmetic: Z[j]*sigma minus C[j]*target. -/
def evalStored (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (j : Fin s) (input : Input F m n) : ArithmeticResult F :=
  let left := dotLoop m (Z j) input.1
  let right := dotLoop n (C j) input.2
  ⟨left.value - right.value, left.multiplications + right.multiplications,
    left.additions + right.additions, left.subtractions + right.subtractions + 1⟩

@[simp] theorem evalStored_value (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (j : Fin s) (input : Input F m n) :
    (evalStored Z C j input).value =
      (∑ col, Z j col * input.1 col) - ∑ i, C j i * input.2 i := by
  simp [evalStored]

@[simp] theorem evalStored_multiplications
    (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (j : Fin s) (input : Input F m n) :
    (evalStored Z C j input).multiplications = m + n := by simp [evalStored]

@[simp] theorem evalStored_additions (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (j : Fin s) (input : Input F m n) :
    (evalStored Z C j input).additions = m + n := by simp [evalStored]

@[simp] theorem evalStored_subtractions
    (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (j : Fin s) (input : Input F m n) :
    (evalStored Z C j input).subtractions = 1 := by simp [evalStored]

/-- Correct prepared coefficients imply the actual arithmetic equals the raw
row/residual dot product.  No raw residual is computed by `evalStored`. -/
theorem stored_value_correct (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (hZ : ∀ j col, Z j col = storedRow A (C j) col)
    (j : Fin s) (input : Input F m n) :
    (evalStored Z C j input).value = rowDot (mvResidual A input.1 input.2) (C j) := by
  rw [evalStored_value]
  simpa only [storedCheck, hZ] using storedCheck_eq A (C j) input.1 input.2

variable [DecidableEq F]

/-- The Boolean oracle bit is produced from the actual stored computation. -/
theorem stored_bit_correct (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (hZ : ∀ j col, Z j col = storedRow A (C j) col)
    (j : Fin s) (input : Input F m n) :
    decide ((evalStored Z C j input).value = 0) =
      rowTest (C j) (mvResidual A input.1 input.2) := by
  rw [stored_value_correct A Z C hZ]
  rfl

/-- Relabel queries while preserving every adaptive branch and leaf. -/
def mapQueries {J X X' Y : Type*} (f : X → X') : QueryTree J X Y → QueryTree J X' Y
  | .leaf y => .leaf y
  | .query j x next => .query j (f x) (fun b => mapQueries f (next b))

structure Execution (Y : Type*) where
  output : Y
  trace : List Bool
  multiplications : ℕ
  additions : ℕ
  subtractions : ℕ

/-- Operational adaptive runner.  Each branch is chosen by the prepared-matrix
arithmetic just executed, and its work counters are accumulated. -/
def storedRun {Y : Type*} (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F) :
    QueryTree (Fin s) (Input F m n) Y → Execution Y
  | .leaf y => ⟨y, [], 0, 0, 0⟩
  | .query j input next =>
      let checked := evalStored Z C j input
      let b := decide (checked.value = 0)
      let rest := storedRun Z C (next b)
      ⟨rest.output, b :: rest.trace,
        checked.multiplications + rest.multiplications,
        checked.additions + rest.additions,
        checked.subtractions + rest.subtractions⟩

/-- Actual stored execution returns the same output as the residual experiment. -/
theorem storedRun_output {Y : Type*} (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (hZ : ∀ j col, Z j col = storedRow A (C j) col)
    (tree : QueryTree (Fin s) (Input F m n) Y) :
    (storedRun Z C tree).output =
      runOutput C (mapQueries (fun input => mvResidual A input.1 input.2) tree) := by
  induction tree with
  | leaf _ => rfl
  | query j input next ih =>
      simp only [storedRun, mapQueries, runOutput, stored_bit_correct A Z C hZ, ih]

/-- Every adaptive transcript bit agrees with the residual experiment. -/
theorem storedRun_trace {Y : Type*} (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (hZ : ∀ j col, Z j col = storedRow A (C j) col)
    (tree : QueryTree (Fin s) (Input F m n) Y) :
    (storedRun Z C tree).trace =
      runBits rowTest C (mapQueries (fun input => mvResidual A input.1 input.2) tree) := by
  induction tree with
  | leaf _ => rfl
  | query j input next ih =>
      simp only [storedRun, mapQueries, runBits, stored_bit_correct A Z C hZ, ih]

/-- Exact field multiplication work for every actual execution, including
zero-query leaves and all adaptive stopping patterns. -/
theorem storedRun_work {Y : Type*}
    (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (tree : QueryTree (Fin s) (Input F m n) Y) :
    (storedRun Z C tree).multiplications = (m+n) * (storedRun Z C tree).trace.length ∧
    (storedRun Z C tree).additions = (m+n) * (storedRun Z C tree).trace.length ∧
    (storedRun Z C tree).subtractions = (storedRun Z C tree).trace.length := by
  induction tree with
  | leaf _ => simp [storedRun]
  | query j input next ih =>
      have h := ih (decide ((evalStored Z C j input).value = 0))
      simp only [storedRun, evalStored_multiplications, evalStored_additions,
        evalStored_subtractions, List.length_cons]
      rw [h.1, h.2.1, h.2.2]
      simp [Nat.mul_succ, Nat.mul_add, Nat.add_comm]

/-- Cost expressed directly in the transcript of the verified residual model. -/
theorem storedRun_work_on_mapped_trace {Y : Type*} (A : Fin n → Fin m → F)
    (Z : Fin s → Fin m → F) (C : Fin s → Fin n → F)
    (hZ : ∀ j col, Z j col = storedRow A (C j) col)
    (tree : QueryTree (Fin s) (Input F m n) Y) :
    (storedRun Z C tree).multiplications = (m+n) *
      (runBits rowTest C (mapQueries (fun input => mvResidual A input.1 input.2) tree)).length := by
  rw [(storedRun_work Z C tree).1, storedRun_trace A Z C hZ]

#print axioms stored_value_correct
#print axioms stored_bit_correct
#print axioms storedRun_output
#print axioms storedRun_trace
#print axioms storedRun_work
#print axioms storedRun_work_on_mapped_trace
end ProgressivePool.StoredCheckExecution
