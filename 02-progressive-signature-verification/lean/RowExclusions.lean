import UniformRow
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProgressivePool
open Finset

/-- Removing `l` sets of size at most `h` removes at most `l*h` points. -/
theorem excluded_union_card {A J : Type*} [DecidableEq A]
    (js : Finset J) (bad : J → Finset A) (h : ℕ)
    (hb : ∀ j ∈ js, (bad j).card ≤ h) :
    (js.biUnion bad).card ≤ js.card * h := by
  calc
    (js.biUnion bad).card ≤ ∑ j ∈ js, (bad j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ js, h := sum_le_sum hb
    _ = js.card * h := by simp

/-- The denominator lower bound is proved from explicit finite exclusions. -/
theorem remaining_card_lower {A J : Type*} [DecidableEq A]
    (space : Finset A) (js : Finset J) (bad : J → Finset A) (h : ℕ)
    (hb : ∀ j ∈ js, (bad j).card ≤ h) :
    space.card - js.card * h ≤ (space \ js.biUnion bad).card := by
  have he := excluded_union_card js bad h hb
  calc
    space.card - js.card * h ≤ space.card - (js.biUnion bad).card :=
      Nat.sub_le_sub_left he _
    _ ≤ (space \ js.biUnion bad).card := le_card_sdiff _ _

/-- Integer form of the conditional probability bound. It avoids division and
is valid even when the conditioning cell is empty. -/
theorem conditioned_count_bound {A J : Type*} [DecidableEq A]
    (space : Finset A) (js : Finset J) (bad : J → Finset A)
    (hit : Finset A) (q h : ℕ)
    (hu : space.card = q*h)
    (hb : ∀ j ∈ js, (bad j).card ≤ h)
    (hh : hit.card ≤ h) :
    (q-js.card) * ((space \ js.biUnion bad) ∩ hit).card ≤
      (space \ js.biUnion bad).card := by
  have hl := remaining_card_lower space js bad h hb
  have hi : ((space \ js.biUnion bad) ∩ hit).card ≤ h :=
    (card_le_card inter_subset_right).trans hh
  calc
    (q-js.card) * ((space \ js.biUnion bad) ∩ hit).card ≤
        (q-js.card)*h := Nat.mul_le_mul_left _ hi
    _ = q*h-js.card*h := Nat.sub_mul _ _ _
    _ ≤ (space \ js.biUnion bad).card := by simpa [hu] using hl

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I]

/-- The concrete uniform-row conditioning inequality, derived from field
surjectivity and finite exclusion counting rather than assumed as a hypothesis. -/
theorem uniform_row_conditioned_count
    (prior : Finset (I → F)) (w : I → F)
    (hp : ∀ v ∈ prior, v ≠ 0) (hw : w ≠ 0) :
    let zeros := fun v : I → F => univ.filter fun c : I → F => rowDot v c = 0
    let remaining := univ \ prior.biUnion zeros
    (Fintype.card F-prior.card) * (remaining ∩ zeros w).card ≤ remaining.card := by
  dsimp
  apply conditioned_count_bound (univ : Finset (I → F)) prior
    (fun v => univ.filter fun c => rowDot v c = 0)
    (univ.filter fun c => rowDot w c = 0) (Fintype.card F)
    (univ.filter fun c => rowDot w c = 0).card
  · simpa [Nat.mul_comm] using (rowDot_zero_card_mul hw).symm
  · intro v hv
    exact (rowDot_zero_card_eq (hp v hv) hw).le
  · exact le_rfl

#print axioms uniform_row_conditioned_count
#print axioms conditioned_count_bound
end ProgressivePool
