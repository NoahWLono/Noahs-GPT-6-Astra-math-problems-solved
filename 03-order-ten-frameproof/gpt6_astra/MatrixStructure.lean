import SearchLemmas
import Mathlib.Data.Fintype.EquivFin

/-!
Structural consequences of the order-ten separating-family specification.
These statements do not prove or refute `OpenProblem10`.
-/

set_option autoImplicit false

namespace GPT6Astra

def ConstantRow (A : BinaryMatrix 10) (r : Fin 10) : Prop :=
  ∀ a b, A r a = A r b

/-- The bit at column `a` occurs nowhere else in this row. -/
def PrivateAt (A : BinaryMatrix 10) (r a : Fin 10) : Prop :=
  ∀ b, b ≠ a → A r b ≠ A r a

def ElementaryRow (A : BinaryMatrix 10) (r : Fin 10) : Prop :=
  ConstantRow A r ∨ ∃ a, PrivateAt A r a

theorem bool_eq_of_ne_common (x y z : Bool) (hx : x ≠ z) (hy : y ≠ z) :
    x = y := by
  cases x <;> cases y <;> cases z <;> simp_all

theorem privateAt_unique (A : BinaryMatrix 10) (r a b : Fin 10)
    (ha : PrivateAt A r a) (hb : PrivateAt A r b) : a = b := by
  by_contra hab
  obtain ⟨c, hca, hcb, _⟩ := exists_fourth_column a b b
  have hba := ha b (Ne.symm hab)
  have hca' := ha c hca
  have hcb' := hb c hcb
  exact hcb' (bool_eq_of_ne_common (A r c) (A r b) (A r a) hca' hba)

theorem privateAt_of_elementary_separatesPair (A : BinaryMatrix 10)
    (r a b c : Fin 10) (hbc : b ≠ c) (helem : ElementaryRow A r)
    (hsep : SeparatesPair A r a b c) : PrivateAt A r a := by
  rcases helem with hconst | ⟨e, he⟩
  · exact False.elim (hsep.1 (hconst a b))
  · by_cases hea : e = a
    · simpa only [hea] using he
    · have hae := he a (Ne.symm hea)
      have hbe : b = e := by
        by_contra hbe
        exact hsep.1 (bool_eq_of_ne_common (A r a) (A r b) (A r e)
          hae (he b hbe))
      have hce : c = e := by
        by_contra hce
        exact hsep.2 (bool_eq_of_ne_common (A r a) (A r c) (A r e)
          hae (he c hce))
      exact False.elim (hbc (hbe.trans hce.symm))

theorem private_row_for_each_column_of_elementary (A : BinaryMatrix 10)
    (hshf : IsSHF A) (helem : ∀ r, ElementaryRow A r) :
    ∀ a, ∃ r, PrivateAt A r a := by
  intro a
  obtain ⟨b, hba, _, _⟩ := exists_fourth_column a a a
  obtain ⟨c, hca, hcb, _⟩ := exists_fourth_column a b b
  obtain ⟨d, hda, hdb, hdc⟩ := exists_fourth_column a b c
  obtain ⟨r, hr⟩ := hshf a b c d (Ne.symm hba) (Ne.symm hca)
    (Ne.symm hda) (Ne.symm hcb) (Ne.symm hdb) (Ne.symm hdc)
  exact ⟨r, privateAt_of_elementary_separatesPair A r a b c
    (Ne.symm hcb) (helem r) ⟨hr.1, hr.2.1⟩⟩

/-- An order-ten separating family with only elementary rows is trivial. -/
theorem isTrivial_of_all_rows_elementary (A : BinaryMatrix 10)
    (hshf : IsSHF A) (helem : ∀ r, ElementaryRow A r) : IsTrivial A := by
  classical
  choose f hf using private_row_for_each_column_of_elementary A hshf helem
  have hfinj : Function.Injective f := by
    intro a b hab
    apply privateAt_unique A (f a) a b (hf a)
    simpa only [hab] using hf b
  let e : Fin 10 ≃ Fin 10 := Equiv.ofBijective f
    ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  have hpriv (r : Fin 10) : PrivateAt A r (e.symm r) := by
    have h := hf (e.symm r)
    change PrivateAt A (e (e.symm r)) (e.symm r) at h
    simpa only [e.apply_symm_apply] using h
  refine ⟨e.symm, fun r => !(A r (e.symm r)), ?_⟩
  intro r c
  by_cases hc : e.symm r = c
  · subst c
    cases h : A r (e.symm r) <;> simp [h]
  · have hne := hpriv r c (Ne.symm hc)
    cases hrc : A r c <;> cases hrp : A r (e.symm r) <;> simp_all

/-- Any nontrivial order-ten separating family has a genuinely nontrivial cut row. -/
theorem exists_non_elementary_row (A : BinaryMatrix 10)
    (hshf : IsSHF A) (hnt : ¬ IsTrivial A) :
    ∃ r, ¬ ConstantRow A r ∧ ¬ ∃ a, PrivateAt A r a := by
  classical
  by_contra h
  apply hnt
  apply isTrivial_of_all_rows_elementary A hshf
  intro r
  by_cases hc : ConstantRow A r
  · exact Or.inl hc
  · right
    by_contra hp
    exact h ⟨r, hc, hp⟩

/-- The designated column never has a private bit, without restrictions on other columns. -/
def NoPrivateAt (A : BinaryMatrix 10) (a : Fin 10) : Prop :=
  ∀ r, ¬ PrivateAt A r a

theorem matching_column_of_not_privateAt (A : BinaryMatrix 10)
    (r a : Fin 10) (h : ¬ PrivateAt A r a) :
    ∃ e, e ≠ a ∧ A r e = A r a := by
  classical
  unfold PrivateAt at h
  push Not at h
  exact h

/-- Only the designated column needs to lack private bits for the two-witness rule. -/
theorem two_rows_separate_pair_of_noPrivateAt (A : BinaryMatrix 10)
    (hshf : IsSHF A) (a b c : Fin 10) (hnp : NoPrivateAt A a)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ r s : Fin 10, r ≠ s ∧ SeparatesPair A r a b c ∧
      SeparatesPair A s a b c := by
  obtain ⟨d, hda, hdb, hdc⟩ := exists_fourth_column a b c
  obtain ⟨r, hr⟩ := hshf a b c d hab hac (Ne.symm hda) hbc
    (Ne.symm hdb) (Ne.symm hdc)
  obtain ⟨e, hea, he⟩ := matching_column_of_not_privateAt A r a (hnp r)
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

/-- Clause-shaped form of the conditional pair bound, for any omitted row. -/
theorem private_or_pair_other_row (A : BinaryMatrix 10) (hshf : IsSHF A)
    (a b c t : Fin 10) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∃ r, PrivateAt A r a) ∨ ∃ r, r ≠ t ∧ SeparatesPair A r a b c := by
  classical
  by_cases hp : ∃ r, PrivateAt A r a
  · exact Or.inl hp
  · have hnp : NoPrivateAt A a := fun r hr => hp ⟨r, hr⟩
    obtain ⟨r, s, hrs, hr, hs⟩ :=
      two_rows_separate_pair_of_noPrivateAt A hshf a b c hnp hab hac hbc
    right
    by_cases hrt : r = t
    · exact ⟨s, fun hst => hrs (hrt.trans hst.symm), hs⟩
    · exact ⟨r, hrt, hr⟩

end GPT6Astra

#print axioms GPT6Astra.isTrivial_of_all_rows_elementary
#print axioms GPT6Astra.exists_non_elementary_row
#print axioms GPT6Astra.two_rows_separate_pair_of_noPrivateAt
#print axioms GPT6Astra.private_or_pair_other_row
