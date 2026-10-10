import ConcreteAdaptiveTail
import Aesop

namespace ProgressivePool
open Finset Classical
variable {F I J : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def spoiledRows (obs : List (Observation J (I → F))) : Finset J :=
  univ.filter fun j => ∃ o ∈ obs, o.row = j ∧ o.input ≠ 0 ∧ o.answer = true

theorem not_mem_spoiledRows (obs : List (Observation J (I → F))) (j : J) :
    j ∉ spoiledRows obs ↔
      ∀ o ∈ obs, o.row = j → o.input ≠ 0 → o.answer = false := by
  simp only [spoiledRows, mem_filter, mem_univ, true_and, not_exists, not_and]
  simp

theorem freshMark_eq (obs : List (Observation J (I → F))) (j : J) (w : I → F) :
    freshMark obs j w = decide (w ≠ 0 ∧ j ∉ spoiledRows obs) := by
  simp only [freshMark, not_mem_spoiledRows]

theorem spoiledRows_append (obs : List (Observation J (I → F)))
    (j : J) (w : I → F) (b : Bool) :
    spoiledRows (obs ++ [⟨j,w,b⟩]) =
      if w ≠ 0 ∧ b = true then insert j (spoiledRows obs) else spoiledRows obs := by
  ext k
  simp only [spoiledRows, mem_filter, mem_univ, true_and,
    List.mem_append, List.mem_singleton]
  split_ifs with h
  · simp only [mem_insert, mem_filter, mem_univ, true_and]
    aesop
  · simp only [mem_filter, mem_univ, true_and]
    aesop

theorem spoiledRows_card_step (obs : List (Observation J (I → F)))
    (j : J) (w : I → F) (b : Bool) :
    (spoiledRows (obs ++ [⟨j,w,b⟩])).card = (spoiledRows obs).card +
      (if freshMark obs j w && b then 1 else 0) := by
  rw [spoiledRows_append, freshMark_eq]
  by_cases hw : w = 0
  · simp [hw]
  · by_cases hj : j ∈ spoiledRows obs
    · simp [hw,hj,insert_eq_of_mem hj]
    · cases b <;> simp [hw,hj,card_insert_of_not_mem hj]

#print axioms spoiledRows_card_step
end ProgressivePool
