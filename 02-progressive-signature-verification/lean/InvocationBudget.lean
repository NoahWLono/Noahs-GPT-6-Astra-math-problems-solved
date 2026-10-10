import SignatureCompiler
import CostAndConfidence

namespace ProgressivePool
open Classical
variable {F I J A Z : Type*} [Field F] [Fintype I]

def bindQueries (tree : QueryTree J (I → F) A) (next : A → QueryTree J (I → F) Z) :
    QueryTree J (I → F) Z :=
  match tree with
  | .leaf a => next a
  | .query j w branches => .query j w (fun b => bindQueries (branches b) next)

theorem bindQueries_height (tree : QueryTree J (I → F) A)
    (next : A → QueryTree J (I → F) Z) (N : ℕ)
    (hnext : ∀ a, queryHeight (next a) ≤ N) :
    queryHeight (bindQueries tree next) ≤ queryHeight tree + N := by
  induction tree with
  | leaf a => simpa [bindQueries,queryHeight] using hnext a
  | query j w branches ih =>
    simp only [bindQueries,queryHeight]
    have h0 := ih false
    have h1 := ih true
    omega

/-- An invocation reserves one slot even if its batch makes zero checks.
There is no constructor that refunds a slot after an interrupted batch. -/
inductive InvocationProgram (J X H Z : Type*) : ℕ → Type _ where
  | stop {r : ℕ} : Z → InvocationProgram J X H Z r
  | invoke {r : ℕ} : QueryTree J X H → (H → InvocationProgram J X H Z r) →
      InvocationProgram J X H Z (r+1)

def invocationCaps (k : ℕ) : {r : ℕ} → InvocationProgram J (I → F) A Z r → Prop
  | _, .stop _ => True
  | _, .invoke batch next => queryHeight batch ≤ k ∧ ∀ a, invocationCaps k (next a)

def flattenInvocations : {r : ℕ} → InvocationProgram J (I → F) A Z r → QueryTree J (I → F) Z
  | _, .stop z => .leaf z
  | _, .invoke batch next => bindQueries batch (fun a => flattenInvocations (next a))

/-- The R*k bound follows from the invocation syntax, including empty/aborted
batches, rather than being a separately assumed total-query restriction. -/
theorem reserved_query_budget {r k : ℕ} (p : InvocationProgram J (I → F) A Z r)
    (hc : invocationCaps k p) : queryHeight (flattenInvocations p) ≤ r*k := by
  induction p with
  | stop z => simp [flattenInvocations,queryHeight]
  | @invoke r batch next ih =>
    have hh := bindQueries_height batch (fun a => flattenInvocations (next a)) (r*k)
      (fun a => ih a (hc.2 a))
    change queryHeight (bindQueries batch (fun a => flattenInvocations (next a))) ≤ (r+1)*k
    have hb := hc.1
    calc
      _ ≤ queryHeight batch + r*k := hh
      _ ≤ k+r*k := Nat.add_le_add_right hb _
      _ = (r+1)*k := by simp [Nat.add_mul,Nat.add_comm]

#print axioms reserved_query_budget
end ProgressivePool
