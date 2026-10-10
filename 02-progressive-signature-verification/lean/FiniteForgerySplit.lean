import FreshSampling

namespace ProgressivePool.FiniteForgerySplit
open Finset Classical
variable {X : Type*} [Fintype X]

noncomputable def ordinaryMass (weight : X → ℚ) (fresh aux valid : X → Bool) : ℚ :=
  ∑ x, if fresh x && aux x && valid x then weight x else 0

noncomputable def progressiveMass {s : ℕ} (weight : X → ℚ) (fresh aux : X → Bool)
    (K : X → Finset (Fin s)) (T : X → ℕ) : ℚ :=
  ∑ x, if fresh x && aux x then weight x * FreshSampling.acceptProbability (K x) (T x) else 0

noncomputable def extraMass {s : ℕ} (weight : X → ℚ) (aux valid : X → Bool)
    (K : X → Finset (Fin s)) (T : X → ℕ) : ℚ :=
  ∑ x, if aux x && !valid x then weight x * FreshSampling.acceptProbability (K x) (T x) else 0

/-- Exact event classification upper bound, with no hardness assumption. The
extra term even allows replayed invalid candidates, making it only larger. -/
theorem progressive_le_ordinary_add_extra {s : ℕ} (hs : 0 < s)
    (weight : X → ℚ) (hw : ∀ x, 0 ≤ weight x) (fresh aux valid : X → Bool)
    (K : X → Finset (Fin s)) (T : X → ℕ) :
    progressiveMass weight fresh aux K T ≤
      ordinaryMass weight fresh aux valid + extraMass weight aux valid K T := by
  rw [progressiveMass,ordinaryMass,extraMass,← sum_add_distrib]
  apply sum_le_sum
  intro x hx
  have hp := FreshSampling.acceptProbability_nonneg (K x) (T x)
  have h1 := FreshSampling.acceptProbability_le_one hs (K x) (T x)
  have hmul := mul_le_mul_of_nonneg_left h1 (hw x)
  have hn := mul_nonneg (hw x) hp
  cases hf : fresh x <;> cases ha : aux x <;> cases hv : valid x <;>
    simp_all

/-- The ordinary-signature term is an explicit named hypothesis. This theorem
is not an EUF simulation or an instantiation of a lattice hardness assumption. -/
theorem full_bound {s : ℕ} (hs : 0 < s)
    (weight : X → ℚ) (hw : ∀ x, 0 ≤ weight x) (fresh aux valid : X → Bool)
    (K : X → Finset (Fin s)) (T : X → ℕ) (baseError verificationError : ℚ)
    (hbase : ordinaryMass weight fresh aux valid ≤ baseError)
    (hextra : extraMass weight aux valid K T ≤ verificationError) :
    progressiveMass weight fresh aux K T ≤ baseError + verificationError :=
  (progressive_le_ordinary_add_extra hs weight hw fresh aux valid K T).trans
    (add_le_add hbase hextra)

#print axioms progressive_le_ordinary_add_extra
#print axioms full_bound
end ProgressivePool.FiniteForgerySplit
