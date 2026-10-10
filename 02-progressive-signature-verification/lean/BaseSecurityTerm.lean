import SignatureCompiler

namespace ProgressivePool
open Finset Classical
set_option maxHeartbeats 800000
variable {F I P : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

noncomputable def ordinaryForgeryMass {s : ℕ}
    (tree : QueryTree (Fin s) (I → F) P) (aux fresh : P → Bool)
    (residual : P → I → F) : ℚ :=
  ∑ bank : Fin s → I → F,
    if fresh (runOutput bank tree) = true ∧ aux (runOutput bank tree) = true ∧
        residual (runOutput bank tree) = 0 then
      1 / (Fintype.card (Fin s → I → F) : ℚ) else 0

noncomputable def progressiveForgeryMass {s : ℕ}
    (tree : QueryTree (Fin s) (I → F) P) (aux fresh : P → Bool)
    (residual : P → I → F) (T : (Fin s → I → F) → ℕ) : ℚ :=
  ∑ bank : Fin s → I → F,
    if fresh (runOutput bank tree) = true ∧ aux (runOutput bank tree) = true then
      (1 / (Fintype.card (Fin s → I → F) : ℚ)) *
        FreshSampling.acceptProbability
          (univ.filter fun j => rowDot (residual (runOutput bank tree)) (bank j) = 0) (T bank)
    else 0

/-- Ordinary-valid fresh forgeries and extra verification errors are separated.
The named base-security hypothesis belongs to the underlying signature game;
this counting theorem neither invents it nor proves a new signature assumption. -/
theorem forgery_split {s : ℕ} (hs : 0 < s)
    (tree : QueryTree (Fin s) (I → F) P) (aux fresh : P → Bool)
    (residual : P → I → F) (T : (Fin s → I → F) → ℕ) :
    progressiveForgeryMass tree aux fresh residual T ≤
      ordinaryForgeryMass tree aux fresh residual + verificationErrorMass tree aux residual T := by
  rw [progressiveForgeryMass, ordinaryForgeryMass, verificationErrorMass, ← sum_add_distrib]
  apply sum_le_sum
  intro bank _
  have hw : (0 : ℚ) ≤ 1 / (Fintype.card (Fin s → I → F) : ℚ) :=
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hp := FreshSampling.acceptProbability_le_one hs
    (univ.filter fun j => rowDot (residual (runOutput bank tree)) (bank j) = 0) (T bank)
  have hn := FreshSampling.acceptProbability_nonneg
    (univ.filter fun j => rowDot (residual (runOutput bank tree)) (bank j) = 0) (T bank)
  have hprod := mul_nonneg hw hn
  by_cases hf : fresh (runOutput bank tree) = true
  · by_cases ha : aux (runOutput bank tree) = true
    · by_cases hz : residual (runOutput bank tree) = 0
      · simp only [hf,ha,hz,true_and,and_self,ite_true,not_true_eq_false,ite_false,add_zero]
        simpa [hz] using mul_le_mul_of_nonneg_left hp hw
      · simp [hf,ha,hz]
    · simp [hf,ha]
  · simp only [hf,false_and,ite_false,zero_add]
    split_ifs <;> simp_all

theorem full_signature_bound {s : ℕ} (hs : 0 < s)
    (tree : QueryTree (Fin s) (I → F) P) (aux fresh : P → Bool)
    (residual : P → I → F) (dummy : I → F) (hdummy : dummy ≠ 0)
    (L u : ℕ) (hdepth : queryHeight tree ≤ L)
    (hfield : L+s < Fintype.card F) (T : (Fin s → I → F) → ℕ)
    (baseError : ℚ)
    (base_signature_security : ordinaryForgeryMass tree aux fresh residual ≤ baseError) :
    progressiveForgeryMass tree aux fresh residual T ≤ baseError +
      ((∑ bank : Fin s → I → F, (((u-1 : ℕ) : ℚ)/(s : ℚ))^(T bank)) /
        (Fintype.card (Fin s → I → F) : ℚ) +
          ((L+s).choose u : ℚ) / ((Fintype.card F-(L+s) : ℕ) : ℚ)^u) := by
  exact (forgery_split hs tree aux fresh residual T).trans
    (add_le_add base_signature_security
      (signature_verification_error_bound hs tree aux residual dummy hdummy L u hdepth hfield T))

#print axioms forgery_split
#print axioms full_signature_bound
end ProgressivePool
