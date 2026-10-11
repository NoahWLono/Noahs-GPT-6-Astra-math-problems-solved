import MatrixStructure

/-!
The finite cut-family representation used to connect binary matrices to SAT.
The definitions and reductions in this file are mathematical, independent of any solver.
-/

set_option autoImplicit false

namespace GPT6Astra

abbrev Cut := Finset (Fin 10)

def cutBit (C : Cut) (a : Fin 10) : Bool := decide (a ∈ C)

def rawCut (A : BinaryMatrix 10) (r : Fin 10) : Cut :=
  Finset.univ.filter (fun a => A r a = true)

/-- Minority-side representative, with column nine excluded in a balanced tie. -/
def CanonicalCut (C : Cut) : Prop :=
  C.card ≤ 5 ∧ (C.card = 5 → (9 : Fin 10) ∉ C)

instance (C : Cut) : Decidable (CanonicalCut C) := inferInstanceAs
  (Decidable (C.card ≤ 5 ∧ (C.card = 5 → (9 : Fin 10) ∉ C)))

def normalizeCut (C : Cut) : Cut := if CanonicalCut C then C else Cᶜ

theorem canonicalCut_compl_iff (C : Cut) : CanonicalCut Cᶜ ↔ ¬ CanonicalCut C := by
  have hcard := Finset.card_add_card_compl C
  simp only [Fintype.card_fin] at hcard
  unfold CanonicalCut
  simp only [Finset.mem_compl, not_not]
  by_cases hmem : (9 : Fin 10) ∈ C <;> simp [hmem] <;> omega

theorem normalizeCut_canonical (C : Cut) : CanonicalCut (normalizeCut C) := by
  unfold normalizeCut
  split_ifs with h
  · exact h
  · exact (canonicalCut_compl_iff C).2 h

theorem normalizeCut_compl (C : Cut) : normalizeCut Cᶜ = normalizeCut C := by
  by_cases h : CanonicalCut C
  · have hc : ¬ CanonicalCut Cᶜ := by
      intro hc
      exact (canonicalCut_compl_iff C).1 hc h
    simp [normalizeCut, h, hc]
  · have hc := (canonicalCut_compl_iff C).2 h
    simp [normalizeCut, h, hc]

theorem normalizeCut_singleton (a : Fin 10) : normalizeCut {a} = {a} := by
  simp [normalizeCut, CanonicalCut]

theorem cutBit_rawCut (A : BinaryMatrix 10) (r a : Fin 10) :
    cutBit (rawCut A r) a = A r a := by
  cases h : A r a <;> simp [cutBit, rawCut, h]

theorem cutBit_compl (C : Cut) (a : Fin 10) : cutBit Cᶜ a = !(cutBit C a) := by
  simp [cutBit]

theorem bool_not_ne_not (x y : Bool) : ((!x) ≠ (!y)) ↔ x ≠ y := by
  cases x <;> cases y <;> decide

theorem cutBit_normalize_ne_iff (C : Cut) (a b : Fin 10) :
    (cutBit (normalizeCut C) a ≠ cutBit (normalizeCut C) b) ↔
      cutBit C a ≠ cutBit C b := by
  unfold normalizeCut
  split_ifs
  · rfl
  · simp only [cutBit_compl]
    exact bool_not_ne_not _ _

def CutSeparates (C : Cut) (a b c d : Fin 10) : Prop :=
  cutBit C a ≠ cutBit C b ∧ cutBit C a ≠ cutBit C c ∧ cutBit C a ≠ cutBit C d

def CutSeparatesPair (C : Cut) (a b c : Fin 10) : Prop :=
  cutBit C a ≠ cutBit C b ∧ cutBit C a ≠ cutBit C c

theorem cutSeparates_normalizedRow_iff (A : BinaryMatrix 10)
    (r a b c d : Fin 10) :
    CutSeparates (normalizeCut (rawCut A r)) a b c d ↔ Separates A r a b c d := by
  simp only [CutSeparates, Separates, cutBit_normalize_ne_iff, cutBit_rawCut]

theorem cutSeparatesPair_normalizedRow_iff (A : BinaryMatrix 10)
    (r a b c : Fin 10) :
    CutSeparatesPair (normalizeCut (rawCut A r)) a b c ↔ SeparatesPair A r a b c := by
  simp only [CutSeparatesPair, SeparatesPair, cutBit_normalize_ne_iff, cutBit_rawCut]

/-- Constant cuts are removed and duplicate rows are identified. -/
def selectedCuts (A : BinaryMatrix 10) : Finset Cut :=
  (Finset.univ.image (fun r => normalizeCut (rawCut A r))).erase ∅

theorem selectedCuts_card_le (A : BinaryMatrix 10) : (selectedCuts A).card ≤ 10 := by
  unfold selectedCuts
  calc
    _ ≤ (Finset.univ.image (fun r => normalizeCut (rawCut A r))).card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    _ ≤ (Finset.univ : Finset (Fin 10)).card := Finset.card_image_le
    _ = 10 := by simp

theorem selectedCuts_canonical (A : BinaryMatrix 10) (C : Cut)
    (hC : C ∈ selectedCuts A) : CanonicalCut C ∧ C ≠ ∅ := by
  obtain ⟨hne, him⟩ := Finset.mem_erase.mp hC
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp him
  exact ⟨hr ▸ normalizeCut_canonical (rawCut A r), hne⟩

theorem normalizedRow_mem_selected_of_separatesPair (A : BinaryMatrix 10)
    (r a b c : Fin 10) (hsep : SeparatesPair A r a b c) :
    normalizeCut (rawCut A r) ∈ selectedCuts A := by
  apply Finset.mem_erase.mpr
  constructor
  · intro h
    have hsep' := (cutSeparatesPair_normalizedRow_iff A r a b c).2 hsep
    rw [h] at hsep'
    simp [CutSeparatesPair, cutBit] at hsep'
  · exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩

theorem selectedCuts_separates (A : BinaryMatrix 10) (hshf : IsSHF A)
    (a b c d : Fin 10) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ C ∈ selectedCuts A, CutSeparates C a b c d := by
  obtain ⟨r, hr⟩ := hshf a b c d hab hac had hbc hbd hcd
  exact ⟨normalizeCut (rawCut A r),
    normalizedRow_mem_selected_of_separatesPair A r a b c ⟨hr.1, hr.2.1⟩,
    (cutSeparates_normalizedRow_iff A r a b c d).2 hr⟩

theorem bool_eq_not_of_ne (x y : Bool) (h : x ≠ y) : x = (!y) := by
  cases x <;> cases y <;> simp_all

theorem rawCut_of_privateAt (A : BinaryMatrix 10) (r a : Fin 10)
    (hp : PrivateAt A r a) : rawCut A r = {a} ∨ rawCut A r = ({a} : Cut)ᶜ := by
  cases ha : A r a
  · right
    ext b
    by_cases hba : b = a
    · subst b
      simp [rawCut, ha]
    · have hb := bool_eq_not_of_ne (A r b) (A r a) (hp b hba)
      simp only [ha, Bool.not_false] at hb
      simp [rawCut, hba, hb]
  · left
    ext b
    by_cases hba : b = a
    · subst b
      simp [rawCut, ha]
    · have hb := bool_eq_not_of_ne (A r b) (A r a) (hp b hba)
      simp only [ha, Bool.not_true] at hb
      simp [rawCut, hba, hb]

theorem normalize_rawCut_of_privateAt (A : BinaryMatrix 10) (r a : Fin 10)
    (hp : PrivateAt A r a) : normalizeCut (rawCut A r) = {a} := by
  rcases rawCut_of_privateAt A r a hp with h | h <;>
    simp only [h, normalizeCut_compl, normalizeCut_singleton]

theorem privateAt_of_normalize_rawCut_singleton (A : BinaryMatrix 10)
    (r a : Fin 10) (h : normalizeCut (rawCut A r) = {a}) : PrivateAt A r a := by
  intro b hba
  have hn : cutBit (normalizeCut (rawCut A r)) b ≠
      cutBit (normalizeCut (rawCut A r)) a := by
    simp [h, cutBit, hba]
  have hn' := (cutBit_normalize_ne_iff (rawCut A r) b a).1 hn
  simpa only [cutBit_rawCut] using hn'

theorem noPrivateAt_of_singleton_not_selected (A : BinaryMatrix 10) (a : Fin 10)
    (h : ({a} : Cut) ∉ selectedCuts A) : NoPrivateAt A a := by
  intro r hp
  apply h
  apply Finset.mem_erase.mpr
  refine ⟨by simp, ?_⟩
  exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, normalize_rawCut_of_privateAt A r a hp⟩

/-- The pair bound remains valid after identifying duplicate and complementary rows. -/
theorem selectedCuts_two_separate_pair (A : BinaryMatrix 10) (hshf : IsSHF A)
    (a b c : Fin 10) (hnp : ({a} : Cut) ∉ selectedCuts A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ C ∈ selectedCuts A, ∃ D ∈ selectedCuts A,
      C ≠ D ∧ CutSeparatesPair C a b c ∧ CutSeparatesPair D a b c := by
  obtain ⟨d, hda, hdb, hdc⟩ := exists_fourth_column a b c
  obtain ⟨r, hr⟩ := hshf a b c d hab hac (Ne.symm hda) hbc
    (Ne.symm hdb) (Ne.symm hdc)
  obtain ⟨e, hea, he⟩ := matching_column_of_not_privateAt A r a
    (noPrivateAt_of_singleton_not_selected A a hnp r)
  have hbe : b ≠ e := by
    intro h
    exact hr.1 (he.symm.trans (congrArg (A r) h.symm))
  have hce : c ≠ e := by
    intro h
    exact hr.2.1 (he.symm.trans (congrArg (A r) h.symm))
  obtain ⟨s, hs⟩ := hshf a b c e hab hac (Ne.symm hea) hbc hbe hce
  refine ⟨normalizeCut (rawCut A r),
    normalizedRow_mem_selected_of_separatesPair A r a b c ⟨hr.1, hr.2.1⟩,
    normalizeCut (rawCut A s),
    normalizedRow_mem_selected_of_separatesPair A s a b c ⟨hs.1, hs.2.1⟩,
    ?_, (cutSeparatesPair_normalizedRow_iff A r a b c).2 ⟨hr.1, hr.2.1⟩,
    (cutSeparatesPair_normalizedRow_iff A s a b c).2 ⟨hs.1, hs.2.1⟩⟩
  intro hcuts
  have hsn : cutBit (normalizeCut (rawCut A s)) a ≠
      cutBit (normalizeCut (rawCut A s)) e := by
    apply (cutBit_normalize_ne_iff (rawCut A s) a e).2
    simpa only [cutBit_rawCut] using hs.2.2
  rw [← hcuts] at hsn
  have hrn := (cutBit_normalize_ne_iff (rawCut A r) a e).1 hsn
  simp only [cutBit_rawCut] at hrn
  exact hrn he.symm

theorem constantRow_of_normalize_rawCut_empty (A : BinaryMatrix 10)
    (r : Fin 10) (h : normalizeCut (rawCut A r) = ∅) : ConstantRow A r := by
  intro a b
  by_contra hab
  have hn : cutBit (normalizeCut (rawCut A r)) a ≠
      cutBit (normalizeCut (rawCut A r)) b := by
    apply (cutBit_normalize_ne_iff (rawCut A r) a b).2
    simpa only [cutBit_rawCut] using hab
  simp [h, cutBit] at hn

theorem selectedCuts_has_nontrivial (A : BinaryMatrix 10)
    (hshf : IsSHF A) (hnt : ¬ IsTrivial A) :
    ∃ C ∈ selectedCuts A, 2 ≤ C.card ∧ C.card ≤ 5 := by
  obtain ⟨r, hnc, hnp⟩ := exists_non_elementary_row A hshf hnt
  let C := normalizeCut (rawCut A r)
  have hne : C ≠ ∅ := by
    intro h
    exact hnc (constantRow_of_normalize_rawCut_empty A r h)
  have hc0 : C.card ≠ 0 := by
    intro h
    exact hne (Finset.card_eq_zero.mp h)
  have hc1 : C.card ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    exact hnp ⟨a, privateAt_of_normalize_rawCut_singleton A r a ha⟩
  refine ⟨C, ?_, by omega, (normalizeCut_canonical (rawCut A r)).1⟩
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩⟩

theorem selectedCuts_has_minimal_nontrivial (A : BinaryMatrix 10)
    (hshf : IsSHF A) (hnt : ¬ IsTrivial A) :
    ∃ C ∈ selectedCuts A, 2 ≤ C.card ∧ C.card ≤ 5 ∧
      ∀ D ∈ selectedCuts A, 2 ≤ D.card → C.card ≤ D.card := by
  obtain ⟨C₀, hC₀, hC₀two, _⟩ := selectedCuts_has_nontrivial A hshf hnt
  have hex : ∃ k : Nat, ∃ C ∈ selectedCuts A, 2 ≤ C.card ∧ C.card = k :=
    ⟨C₀.card, C₀, hC₀, hC₀two, rfl⟩
  obtain ⟨C, hC, hCtwo, hCeq⟩ := Nat.find_spec hex
  refine ⟨C, hC, hCtwo, (selectedCuts_canonical A C hC).1.1, ?_⟩
  intro D hD hDtwo
  rw [hCeq]
  exact Nat.find_min' hex ⟨D, hD, hDtwo, rfl⟩

theorem selectedCuts_weights_at_minimum_five (A : BinaryMatrix 10)
    (hmin : ∀ D ∈ selectedCuts A, 2 ≤ D.card → 5 ≤ D.card)
    (D : Cut) (hD : D ∈ selectedCuts A) : D.card = 1 ∨ D.card = 5 := by
  obtain ⟨hcanon, hne⟩ := selectedCuts_canonical A D hD
  have hc0 : D.card ≠ 0 := by
    intro h
    exact hne (Finset.card_eq_zero.mp h)
  have hle := hcanon.1
  by_cases hDtwo : 2 ≤ D.card
  · have hlo := hmin D hD hDtwo
    right
    omega
  · left
    omega

end GPT6Astra

#print axioms GPT6Astra.selectedCuts_card_le
#print axioms GPT6Astra.selectedCuts_separates
#print axioms GPT6Astra.selectedCuts_two_separate_pair
#print axioms GPT6Astra.selectedCuts_has_minimal_nontrivial
