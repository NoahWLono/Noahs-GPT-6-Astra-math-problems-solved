import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi

/-! Exact finite counting for the actual uniform finite-field row distribution.
No conditional-probability or soundness premise is postulated. -/
namespace ProgressivePool
open Finset

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

def rowDot (w : I → F) : (I → F) →+ F where
  toFun c := ∑ i, c i * w i
  map_zero' := by simp
  map_add' c d := by simp [add_mul, Finset.sum_add_distrib]

theorem rowDot_surjective {w : I → F} (hw : w ≠ 0) :
    Function.Surjective (rowDot w) := by
  have hi : ∃ i, w i ≠ 0 := by
    by_contra h
    apply hw
    funext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := hi
  intro y
  refine ⟨Pi.single i (y / w i), ?_⟩
  simp [rowDot, Pi.single_apply, hi]

theorem rowDot_fiber_card {w : I → F} (hw : w ≠ 0) (a b : F) :
    (univ.filter fun c : I → F => rowDot w c = a).card =
    (univ.filter fun c : I → F => rowDot w c = b).card := by
  apply AddMonoidHom.card_fiber_eq_of_mem_range (rowDot w)
  · exact rowDot_surjective hw a
  · exact rowDot_surjective hw b

theorem rowDot_zero_card_mul {w : I → F} (hw : w ≠ 0) :
    (univ.filter fun c : I → F => rowDot w c = 0).card * Fintype.card F =
      Fintype.card (I → F) := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (I → F))) (t := (univ : Finset F))
    (f := rowDot w) (by simp)
  simp only [card_univ] at h
  rw [h]
  simp_rw [rowDot_fiber_card hw _ 0]
  simp [Nat.mul_comm]

theorem rowDot_zero_card_eq {w v : I → F} (hw : w ≠ 0) (hv : v ≠ 0) :
    (univ.filter fun c : I → F => rowDot w c = 0).card =
      (univ.filter fun c : I → F => rowDot v c = 0).card := by
  exact Nat.eq_of_mul_eq_mul_right (Fintype.card_pos_iff.mpr inferInstance)
    ((rowDot_zero_card_mul hw).trans (rowDot_zero_card_mul hv).symm)

#print axioms rowDot_zero_card_mul
end ProgressivePool
