import SignatureCompiler
import GlobalSignatureCompiler

namespace ProgressivePool
open Finset Classical
variable {C : Type*} [Fintype C]

theorem average_pointwise_bound (weights loss confidence : C → ℚ) (delta : ℚ)
    (hw : ∀ c, 0 ≤ weights c) (hnorm : ∑ c, weights c = 1)
    (hb : ∀ c, loss c ≤ confidence c + delta) :
    (∑ c, weights c * loss c) ≤ (∑ c, weights c * confidence c) + delta := by
  calc
    _ ≤ ∑ c, weights c * (confidence c + delta) :=
      sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hb c) (hw c))
    _ = _ := by simp_rw [mul_add]; rw [sum_add_distrib,← sum_mul,hnorm,one_mul]

variable {F I P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

/-- Explicit finite distribution of adversary/environment tapes, chosen
independently before the uniformly sampled checking bank. The loss is the
actual finite mixture, not a claim that adaptive queries are independent. -/
theorem randomized_signature_verification_error {s : ℕ} (hs : 0 < s)
    (trees : C → QueryTree (Fin s) (I → F) P) (weights : C → ℚ)
    (hw : ∀ c, 0 ≤ weights c) (hnorm : ∑ c, weights c = 1)
    (aux : P → Bool) (residual : P → I → F) (dummy : I → F) (hdummy : dummy ≠ 0)
    (L u : ℕ) (hdepth : ∀ c, queryHeight (trees c) ≤ L)
    (hfield : L+s < Fintype.card F) (T : C → (Fin s → I → F) → ℕ) :
    (∑ c, weights c * verificationErrorMass (trees c) aux residual (T c)) ≤
      (∑ c, weights c *
        ((∑ bank : Fin s → I → F, (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T c bank)) /
          (Fintype.card (Fin s → I → F) : ℚ))) +
      ((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u := by
  apply average_pointwise_bound weights _ _ _ hw hnorm
  intro c
  exact signature_verification_error_bound hs (trees c) aux residual dummy hdummy
    L u (hdepth c) hfield (T c)

#print axioms average_pointwise_bound
#print axioms randomized_signature_verification_error
end ProgressivePool
