import CryptographyResearch
import Mathlib.Data.Fintype.Card

/-!
Elementary conditional search reductions for the order-ten specification.
These statements do not prove or refute `OpenProblem10`.
-/

namespace GPT6Astra

/-- Every bit in every row is shared with at least one other column. -/
def NoPrivateBit (A : BinaryMatrix 10) : Prop :=
  ∀ r a, ∃ e, e ≠ a ∧ A r e = A r a

/-- A row separates the designated column from each of two others. -/
def SeparatesPair (A : BinaryMatrix 10) (r a b c : Fin 10) : Prop :=
  A r a ≠ A r b ∧ A r a ≠ A r c

theorem exists_fourth_column (a b c : Fin 10) :
    ∃ d : Fin 10, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  have hcard : ({a, b, c} : Finset (Fin 10)).card <
      (Finset.univ : Finset (Fin 10)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_three (by decide : 3 < 10)
  obtain ⟨d, _, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨d, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hd⟩

/-- The no-private-bit condition forces two separate witnesses for each pair. -/
theorem two_rows_separate_pair (A : BinaryMatrix 10)
    (hshf : IsSHF A) (hnp : NoPrivateBit A)
    (a b c : Fin 10) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ r s : Fin 10, r ≠ s ∧ SeparatesPair A r a b c ∧
      SeparatesPair A s a b c := by
  obtain ⟨d, hda, hdb, hdc⟩ := exists_fourth_column a b c
  obtain ⟨r, hr⟩ := hshf a b c d hab hac (Ne.symm hda) hbc
    (Ne.symm hdb) (Ne.symm hdc)
  obtain ⟨e, hea, he⟩ := hnp r a
  have hbe : b ≠ e := by
    intro h
    exact hr.1 (he.symm.trans (congrArg (A r) h.symm))
  have hce : c ≠ e := by
    intro h
    exact hr.2.1 (he.symm.trans (congrArg (A r) h.symm))
  obtain ⟨s, hs⟩ := hshf a b c e hab hac (Ne.symm hea) hbc hbe hce
  refine ⟨r, s, ?_, ⟨hr.1, hr.2.1⟩, ⟨hs.1, hs.2.1⟩⟩
  intro hrs
  subst s
  exact hs.2.2 he.symm

def columnDistance (A : BinaryMatrix 10) (a b : Fin 10) : Nat :=
  ((Finset.univ : Finset (Fin 10)).filter (fun r => A r a ≠ A r b)).card

/-- A conditional pruning rule: every two columns differ in at least four rows. -/
theorem columnDistance_ge_four (A : BinaryMatrix 10)
    (hshf : IsSHF A) (hnp : NoPrivateBit A)
    (a b : Fin 10) (hab : a ≠ b) : 4 ≤ columnDistance A a b := by
  obtain ⟨c, hca, hcb, _⟩ := exists_fourth_column a b b
  have hac := Ne.symm hca
  have hbc := Ne.symm hcb
  obtain ⟨r, s, hrs, hr, hs⟩ := two_rows_separate_pair A hshf hnp a b c hab hac hbc
  obtain ⟨t, u, htu, ht, hu⟩ := two_rows_separate_pair A hshf hnp b a c
    (Ne.symm hab) hbc hac
  have hcross (x y : Fin 10) (hx : SeparatesPair A x a b c)
      (hy : SeparatesPair A y b a c) : x ≠ y := by
    intro hxy
    subst y
    cases hxa : A x a <;> cases hxb : A x b <;> cases hxc : A x c <;>
      simp_all [SeparatesPair]
  have hrt := hcross r t hr ht
  have hru := hcross r u hr hu
  have hst := hcross s t hs ht
  have hsu := hcross s u hs hu
  have hcard : ({r, s, t, u} : Finset (Fin 10)).card = 4 := by
    simp [hrs, hrt, hru, hst, hsu, htu]
  have hsub : ({r, s, t, u} : Finset (Fin 10)) ⊆
      (Finset.univ.filter (fun x => A x a ≠ A x b)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with h | h | h | h
    · subst x
      exact hr.1
    · subst x
      exact hs.1
    · subst x
      exact Ne.symm ht.1
    · subst x
      exact Ne.symm hu.1
  unfold columnDistance
  rw [← hcard]
  exact Finset.card_le_card hsub

end GPT6Astra

#print axioms GPT6Astra.two_rows_separate_pair
#print axioms GPT6Astra.columnDistance_ge_four
