import AdaptiveTranscript

namespace ProgressivePool
open Finset
variable {J : Type*} [DecidableEq J]

/-- True labels mean a zero response on a nonzero residual. -/
def spoiledAfter : Finset J → List (J × Bool) → Finset J
  | s, [] => s
  | s, (j,b) :: xs => spoiledAfter (if b then insert j s else s) xs

def firstSpoilCount : Finset J → List (J × Bool) → ℕ
  | _, [] => 0
  | s, (j,b) :: xs =>
    (if b && decide (j ∉ s) then 1 else 0) +
      firstSpoilCount (if b then insert j s else s) xs

theorem spoiledAfter_card (s : Finset J) (xs : List (J × Bool)) :
    (spoiledAfter s xs).card = s.card + firstSpoilCount s xs := by
  induction xs generalizing s with
  | nil => simp [spoiledAfter, firstSpoilCount]
  | cons x xs ih =>
    rcases x with ⟨j,b⟩
    cases b with
    | false => simpa [spoiledAfter, firstSpoilCount] using ih s
    | true =>
      by_cases hj : j ∈ s
      · simpa [spoiledAfter, firstSpoilCount, hj, insert_eq_of_mem hj] using ih s
      · simpa [spoiledAfter, firstSpoilCount, hj, card_insert_of_not_mem hj,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (insert j s)

theorem mem_spoiledAfter (s : Finset J) (xs : List (J × Bool)) (j : J) :
    j ∈ spoiledAfter s xs ↔ j ∈ s ∨ (j,true) ∈ xs := by
  induction xs generalizing s with
  | nil => simp [spoiledAfter]
  | cons x xs ih =>
    rcases x with ⟨i,b⟩
    cases b <;> simp [spoiledAfter, ih, or_assoc, or_left_comm, or_comm, eq_comm]

/-- Every final-zero row is spoiled by the end of the virtual pass. This is a
pure counting fact; no independence assumption appears. -/
theorem final_zero_rows_le_first_spoils [Fintype J]
    (prior : List (J × Bool)) (zero : J → Bool) :
    (univ.filter fun j => zero j = true).card ≤
      firstSpoilCount ∅ (prior ++ (univ.toList.map fun j => (j,zero j))) := by
  have hs : (univ.filter fun j => zero j = true) ⊆
      spoiledAfter ∅ (prior ++ (univ.toList.map fun j => (j,zero j))) := by
    intro j hj
    have hz : zero j = true := (mem_filter.mp hj).2
    apply (mem_spoiledAfter _ _ j).mpr
    right
    apply List.mem_append.mpr
    right
    apply List.mem_map.mpr
    exact ⟨j, by simp, by simp [hz]⟩
  have hc := card_le_card hs
  simpa [spoiledAfter_card] using hc

#print axioms final_zero_rows_le_first_spoils
end ProgressivePool
