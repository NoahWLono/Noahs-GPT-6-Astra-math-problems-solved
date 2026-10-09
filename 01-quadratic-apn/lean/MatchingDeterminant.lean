import PfaffianMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option maxHeartbeats 500000
namespace MatchingDeterminant
open scoped BigOperators
open Equiv
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev F := ZMod 2

def weight (M : Matrix ι ι F) (σ : Perm ι) : F := ∏ i, M (σ i) i

theorem weight_inv (M : Matrix ι ι F) (hs : ∀ i j, M i j = M j i) (σ : Perm ι) :
    weight M σ⁻¹ = weight M σ := by
  unfold weight
  rw [← Equiv.prod_comp σ (fun i => M (σ⁻¹ i) i)]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Perm.inv_apply_self] using hs i (σ i)

theorem det_eq_sum_weight (M : Matrix ι ι F) : M.det = ∑ σ : Perm ι, weight M σ := by
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;>
    simp [h, Units.smul_def, weight, CharTwo.neg_eq]

theorem sum_noninvolutions (M : Matrix ι ι F) (hs : ∀ i j, M i j = M j i) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Perm ι => σ⁻¹ ≠ σ), weight M σ = 0 := by
  refine Finset.sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
  · intro σ _
    rw [weight_inv M hs]
    exact CharTwo.add_self_eq_zero _
  · intro σ hσ _
    exact (Finset.mem_filter.mp hσ).2
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inv_inv]
    exact fun h => (Finset.mem_filter.mp hσ).2 h.symm
  · intro σ _
    exact inv_inv σ

def involutions : Finset (Perm ι) := Finset.univ.filter (fun σ => σ⁻¹ = σ)
def matchings : Finset (Perm ι) := involutions.filter (fun σ => ∀ i, σ i ≠ i)

theorem mem_matchings (σ : Perm ι) :
    σ ∈ matchings ↔ σ⁻¹ = σ ∧ ∀ i, σ i ≠ i := by
  simp [matchings, involutions]

theorem det_eq_involutions (M : Matrix ι ι F) (hs : ∀ i j, M i j = M j i) :
    M.det = ∑ σ ∈ involutions, weight M σ := by
  rw [det_eq_sum_weight]
  have h := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Perm ι))) (p := fun σ => σ⁻¹ = σ) (f := weight M)
  rw [sum_noninvolutions M hs, add_zero] at h
  exact h.symm

theorem det_eq_matchings (M : Matrix ι ι F)
    (hs : ∀ i j, M i j = M j i) (hd : ∀ i, M i i = 0) :
    M.det = ∑ σ ∈ matchings, weight M σ := by
  rw [det_eq_involutions M hs]
  unfold matchings
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : ∀ i, σ i ≠ i
  · simp [h]
  · simp only [h, ↓reduceIte]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hi, hd]

#print axioms det_eq_matchings
end MatchingDeterminant
