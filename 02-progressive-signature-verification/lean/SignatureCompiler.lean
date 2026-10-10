import UniformPoolEndpoint
import StoredRows

namespace ProgressivePool
open Finset Classical
set_option maxHeartbeats 800000
variable {F I P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

def mapOutput {J X A B : Type*} (f : A → B) : QueryTree J X A → QueryTree J X B
  | .leaf a => .leaf (f a)
  | .query j x next => .query j x (fun b => mapOutput f (next b))

theorem runOutput_map {s : ℕ} {A B : Type*} (f : A → B)
    (tree : QueryTree (Fin s) (I → F) A) (bank : Fin s → I → F) :
    runOutput bank (mapOutput f tree) = f (runOutput bank tree) := by
  induction tree with
  | leaf _ => rfl
  | query j x next ih => simp [mapOutput,runOutput,ih]

theorem queryHeight_map {J A B : Type*} (f : A → B)
    (tree : QueryTree J (I → F) A) : queryHeight (mapOutput f tree) = queryHeight tree := by
  induction tree with
  | leaf _ => rfl
  | query j x next ih => simp [mapOutput,queryHeight,ih]

/-- The error experiment retains all auxiliary checks. Zero residuals are
ordinary-valid when Aux holds and therefore do not count as verification errors. -/
noncomputable def verificationErrorMass {s : ℕ}
    (tree : QueryTree (Fin s) (I → F) P) (aux : P → Bool) (residual : P → I → F)
    (T : (Fin s → I → F) → ℕ) : ℚ :=
  ∑ bank : Fin s → I → F,
    if aux (runOutput bank tree) = true ∧ residual (runOutput bank tree) ≠ 0 then
      (1 / (Fintype.card (Fin s → I → F) : ℚ)) *
        FreshSampling.acceptProbability
          (univ.filter fun j => rowDot (residual (runOutput bank tree)) (bank j) = 0) (T bank)
    else 0

/-- Full one-epoch verification-error endpoint, with arbitrary signature outputs
(including valid outputs and auxiliary-check failures). The nonzero dummy only
repairs leaves in the proof and is not part of the verification algorithm. -/
theorem signature_verification_error_bound {s : ℕ} (hs : 0 < s)
    (tree : QueryTree (Fin s) (I → F) P) (aux : P → Bool) (residual : P → I → F)
    (dummy : I → F) (hdummy : dummy ≠ 0)
    (L u : ℕ) (hdepth : queryHeight tree ≤ L)
    (hfield : L+s < Fintype.card F) (T : (Fin s → I → F) → ℕ) :
    verificationErrorMass tree aux residual T ≤
      (∑ bank : Fin s → I → F, (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T bank)) /
        (Fintype.card (Fin s → I → F) : ℚ) +
          ((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u := by
  let repair : P → I → F := fun p => if residual p = 0 then dummy else residual p
  let repaired := mapOutput repair tree
  have hn : ∀ bank, runOutput bank repaired ≠ 0 := by
    intro bank
    rw [runOutput_map]
    dsimp [repair]
    split_ifs with h
    · exact hdummy
    · exact h
  have hh : queryHeight repaired ≤ L := by simpa [repaired, queryHeight_map] using hdepth
  have hb := uniform_pool_progressive hs repaired L u hh hn hfield T
  apply le_trans _ hb
  rw [verificationErrorMass, FreshSampling.acceptMass_eq]
  apply sum_le_sum
  intro bank _
  by_cases he : aux (runOutput bank tree) = true ∧ residual (runOutput bank tree) ≠ 0
  · simp only [he, ite_true]
    have hr : runOutput bank repaired = residual (runOutput bank tree) := by
      simp [repaired,runOutput_map,repair,he.2]
    have hk : (univ.filter fun j => rowDot (residual (runOutput bank tree)) (bank j) = 0) =
        finalZeroRows repaired bank := by simp [finalZeroRows,hr]
    rw [hk]
    simp [he.1,he.2]
  · simp only [he, ite_false]
    exact mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _))
      (FreshSampling.acceptProbability_nonneg _ _)

#print axioms signature_verification_error_bound
end ProgressivePool
