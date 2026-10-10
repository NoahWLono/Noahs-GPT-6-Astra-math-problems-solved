import FieldTranscript

namespace ProgressivePool
open Finset Classical
variable {J K : Type*} [Fintype J] [DecidableEq J] [DecidableEq K]

theorem product_cell_local_bound (cells : J → Finset K) (j : J)
    (hit : Finset K) (d : ℕ)
    (local_bound : d * ((cells j) ∩ hit).card ≤ (cells j).card) :
    d * ((Fintype.piFinset cells).filter fun bank => bank j ∈ hit).card ≤
      (Fintype.piFinset cells).card := by
  let update := Function.update cells j ((cells j) ∩ hit)
  have hu : Fintype.piFinset update =
      (Fintype.piFinset cells).filter fun bank => bank j ∈ hit := by
    rw [Fintype.piFinset_update_eq_filter_piFinset_mem cells j inter_subset_left]
    ext bank
    simp only [mem_filter, mem_inter]
    constructor
    · rintro ⟨hb, _, hh⟩
      exact ⟨hb,hh⟩
    · rintro ⟨hb,hh⟩
      exact ⟨hb,(Fintype.mem_piFinset.mp hb) j,hh⟩
  rw [← hu, Fintype.card_piFinset, Fintype.card_piFinset]
  rw [← prod_erase_mul univ (fun i => (update i).card) (mem_univ j)]
  rw [← prod_erase_mul univ (fun i => (cells i).card) (mem_univ j)]
  have he : (∏ i ∈ univ.erase j, (update i).card) =
      ∏ i ∈ univ.erase j, (cells i).card := by
    apply prod_congr rfl
    intro i hi
    simp [update, (mem_erase.mp hi).1]
  rw [he]
  have hj : (update j).card = ((cells j) ∩ hit).card := by simp [update]
  rw [hj]
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    Nat.mul_le_mul_left (∏ i ∈ univ.erase j, (cells i).card) local_bound

#print axioms product_cell_local_bound
end ProgressivePool
