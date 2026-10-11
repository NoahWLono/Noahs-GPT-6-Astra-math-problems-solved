import CutFamilies
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace GPT6Astra

def rowWeight (A : BinaryMatrix 10) (r : Fin 10) : Nat := (rawCut A r).card

def countOnes (A : BinaryMatrix 10) (r : Fin 10) : Nat :=
  ∑ c : Fin 10, (A r c).toNat

def Shape (A : BinaryMatrix 10) (k : Nat) : Prop :=
  ∀ r, countOnes A r ≤ 5 ∧ (countOnes A r ≤ 1 ∨ k ≤ countOnes A r)

def FixedRow (A : BinaryMatrix 10) (k : Nat) : Prop :=
  ∀ c, A 0 c = decide (c.val < k)

theorem countOnes_eq_rowWeight (A : BinaryMatrix 10) (r : Fin 10) :
    countOnes A r = rowWeight A r := by
  have hb (c : Fin 10) : (A r c).toNat = if A r c = true then 1 else 0 := by
    cases A r c <;> rfl
  simp only [countOnes, hb, rowWeight, rawCut, Finset.sum_boole]
  simp

def normalizedMatrix (A : BinaryMatrix 10) : BinaryMatrix 10 :=
  fun r c => cutBit (normalizeCut (rawCut A r)) c

theorem normalizedMatrix_isSHF (A : BinaryMatrix 10) (hshf : IsSHF A) :
    IsSHF (normalizedMatrix A) := by
  intro a b c d hab hac had hbc hbd hcd
  obtain ⟨r, hr⟩ := hshf a b c d hab hac had hbc hbd hcd
  exact ⟨r, (cutSeparates_normalizedRow_iff A r a b c d).2 hr⟩

theorem rawCut_normalizedMatrix (A : BinaryMatrix 10) (r : Fin 10) :
    rawCut (normalizedMatrix A) r = normalizeCut (rawCut A r) := by
  ext c
  change c ∈ Finset.univ.filter (fun a => normalizedMatrix A r a = true) ↔
    c ∈ normalizeCut (rawCut A r)
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change decide (c ∈ normalizeCut (rawCut A r)) = true ↔ c ∈ normalizeCut (rawCut A r)
  simp only [decide_eq_true_eq]

def permuteMatrix (A : BinaryMatrix 10) (q p : Fin 10 ≃ Fin 10) : BinaryMatrix 10 :=
  fun r c => A (q r) (p c)

theorem permuteMatrix_isSHF (A : BinaryMatrix 10) (hshf : IsSHF A)
    (q p : Fin 10 ≃ Fin 10) : IsSHF (permuteMatrix A q p) := by
  intro a b c d hab hac had hbc hbd hcd
  obtain ⟨r, hr⟩ := hshf (p a) (p b) (p c) (p d)
    (fun h => hab (p.injective h)) (fun h => hac (p.injective h))
    (fun h => had (p.injective h)) (fun h => hbc (p.injective h))
    (fun h => hbd (p.injective h)) (fun h => hcd (p.injective h))
  refine ⟨q.symm r, ?_⟩
  simpa only [Separates, permuteMatrix, q.apply_symm_apply] using hr

theorem rowWeight_permuteMatrix (A : BinaryMatrix 10) (q p : Fin 10 ≃ Fin 10)
    (r : Fin 10) : rowWeight (permuteMatrix A q p) r = rowWeight A (q r) := by
  have heq : rawCut (permuteMatrix A q p) r = (rawCut A (q r)).image p.symm := by
    ext c
    change c ∈ Finset.univ.filter (fun a => permuteMatrix A q p r a = true) ↔
      c ∈ (rawCut A (q r)).image p.symm
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hc
      refine ⟨p c, ?_, p.symm_apply_apply c⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
    · rintro ⟨a, ha, he⟩
      have ha' := (Finset.mem_filter.mp ha).2
      have he' : a = p c := by
        have h := congrArg p he
        simpa only [p.apply_symm_apply] using h
      change A (q r) (p c) = true
      simpa only [he'] using ha'
  unfold rowWeight
  rw [heq, Finset.card_image_of_injective _ p.symm.injective]

theorem countOnes_permuteMatrix (A : BinaryMatrix 10) (q p : Fin 10 ≃ Fin 10)
    (r : Fin 10) : countOnes (permuteMatrix A q p) r = countOnes A (q r) := by
  simp only [countOnes_eq_rowWeight, rowWeight_permuteMatrix]

theorem shape_permuteMatrix (A : BinaryMatrix 10) (k : Nat) (h : Shape A k)
    (q p : Fin 10 ≃ Fin 10) : Shape (permuteMatrix A q p) k := by
  intro r
  simpa only [countOnes_permuteMatrix] using h (q r)

theorem fixedRow_permuteMatrix (A : BinaryMatrix 10) (k : Nat) (h : FixedRow A k)
    (q p : Fin 10 ≃ Fin 10) (hq : q 0 = 0)
    (hp : ∀ c, (p c).val < k ↔ c.val < k) : FixedRow (permuteMatrix A q p) k := by
  intro c
  change A (q 0) (p c) = decide (c.val < k)
  rw [hq, h (p c)]
  simp only [hp c]

def maskRow (m : Fin 1024) (c : Fin 10) : Bool := Nat.testBit m.val c.val

def maskWeight (m : Fin 1024) : Nat :=
  countOnes (fun _ c => maskRow m c) 0

/-- Every forbidden ten-bit mask differs from every row of a matrix satisfying `Shape`. -/
theorem shape_excludes_forbidden_mask (A : BinaryMatrix 10) (k : Nat)
    (hshape : Shape A k) (r : Fin 10) (m : Fin 1024)
    (hbad : 5 < maskWeight m ∨ (1 < maskWeight m ∧ maskWeight m < k)) :
    ¬ ∀ c, A r c = maskRow m c := by
  intro heq
  have hcount : countOnes A r = maskWeight m := by
    unfold countOnes maskWeight
    apply Finset.sum_congr rfl
    intro c _
    rw [heq c]
  obtain ⟨hle, hlo⟩ := hshape r
  rw [hcount] at hle hlo
  omega

theorem shape_has_mask_mismatch (A : BinaryMatrix 10) (k : Nat)
    (hshape : Shape A k) (r : Fin 10) (m : Fin 1024)
    (hbad : 5 < maskWeight m ∨ (1 < maskWeight m ∧ maskWeight m < k)) :
    ∃ c, A r c ≠ maskRow m c := by
  classical
  have h := shape_excludes_forbidden_mask A k hshape r m hbad
  push Not at h
  exact h

def initialCut (k : Nat) : Cut := Finset.univ.filter (fun c => c.val < k)

theorem initialCut_card (k : Nat) (hk2 : 2 ≤ k) (hk5 : k ≤ 5) :
    (initialCut k).card = k := by
  have hcases : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> decide

theorem exists_perm_to_initialCut (C : Cut) (k : Nat) (hC : C.card = k)
    (hk2 : 2 ≤ k) (hk5 : k ≤ 5) :
    ∃ p : Fin 10 ≃ Fin 10, ∀ c, p c ∈ C ↔ c.val < k := by
  classical
  let e : {c // c ∈ initialCut k} ≃ {c // c ∈ C} :=
    Fintype.equivOfCardEq (by simpa using (initialCut_card k hk2 hk5).trans hC.symm)
  refine ⟨e.extendSubtype, ?_⟩
  intro c
  have hm : e.extendSubtype c ∈ C ↔ c ∈ initialCut k := by
    constructor
    · intro hc
      by_contra hci
      exact e.extendSubtype_not_mem c hci hc
    · exact e.extendSubtype_mem c
  simpa only [initialCut, Finset.mem_filter, Finset.mem_univ, true_and] using hm

theorem exists_normalized_matrix (A : BinaryMatrix 10)
    (hshf : IsSHF A) (hnt : ¬ IsTrivial A) :
    ∃ (k : Nat) (B : BinaryMatrix 10),
      2 ≤ k ∧ k ≤ 5 ∧ IsSHF B ∧ Shape B k ∧ FixedRow B k := by
  classical
  obtain ⟨C, hC, hCtwo, hCfive, hmin⟩ := selectedCuts_has_minimal_nontrivial A hshf hnt
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hC).2
  obtain ⟨p, hp⟩ := exists_perm_to_initialCut C C.card rfl hCtwo hCfive
  let N := normalizedMatrix A
  have hN : IsSHF N := normalizedMatrix_isSHF A hshf
  have hshape : Shape N C.card := by
    intro s
    rw [countOnes_eq_rowWeight]
    change (rawCut (normalizedMatrix A) s).card ≤ 5 ∧
      ((rawCut (normalizedMatrix A) s).card ≤ 1 ∨ C.card ≤ (rawCut (normalizedMatrix A) s).card)
    rw [rawCut_normalizedMatrix]
    refine ⟨(normalizeCut_canonical (rawCut A s)).1, ?_⟩
    by_cases hsmall : (normalizeCut (rawCut A s)).card ≤ 1
    · exact Or.inl hsmall
    · right
      apply hmin (normalizeCut (rawCut A s))
      · apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩⟩
        intro hz
        simp only [hz, Finset.card_empty] at hsmall
        omega
      · omega
  let q := Equiv.swap (0 : Fin 10) r
  refine ⟨C.card, permuteMatrix N q p, hCtwo, hCfive,
    permuteMatrix_isSHF N hN q p, shape_permuteMatrix N C.card hshape q p, ?_⟩
  intro c
  change cutBit (normalizeCut (rawCut A (q 0))) (p c) = decide (c.val < C.card)
  have hq : q 0 = r := Equiv.swap_apply_left _ _
  rw [hq, hr]
  simp only [cutBit, hp c]

def AnchorZero (A : BinaryMatrix 10) : Prop :=
  ∀ r : Fin 10, r ≠ 0 → A r 0 = false

def anchoredMatrix (A : BinaryMatrix 10) : BinaryMatrix 10 :=
  complementRows A (fun r => if r = 0 then false else A r 0)

theorem anchoredMatrix_isSHF (A : BinaryMatrix 10) (h : IsSHF A) :
    IsSHF (anchoredMatrix A) :=
  (isSHF_complementRows_iff A _).2 h

theorem anchoredMatrix_fixedRow (A : BinaryMatrix 10) (k : Nat)
    (h : FixedRow A k) : FixedRow (anchoredMatrix A) k := by
  intro c
  simpa [anchoredMatrix, complementRows] using h c

theorem anchoredMatrix_anchorZero (A : BinaryMatrix 10) : AnchorZero (anchoredMatrix A) := by
  intro r hr
  simp [anchoredMatrix, complementRows, hr]

theorem anchorZero_permuteMatrix (A : BinaryMatrix 10) (h : AnchorZero A)
    (q p : Fin 10 ≃ Fin 10) (hq : q 0 = 0) (hp : p 0 = 0) :
    AnchorZero (permuteMatrix A q p) := by
  intro r hr
  change A (q r) (p 0) = false
  rw [hp]
  apply h
  intro hqr
  exact hr (q.injective (hqr.trans hq.symm))

/-- Row complementation anchors column zero below the distinguished first row. -/
theorem exists_anchor_normalized_matrix (A : BinaryMatrix 10)
    (hshf : IsSHF A) (hnt : ¬ IsTrivial A) :
    ∃ (k : Nat) (B : BinaryMatrix 10),
      2 ≤ k ∧ k ≤ 5 ∧ IsSHF B ∧ FixedRow B k ∧ AnchorZero B := by
  obtain ⟨k, N, hk2, hk5, hN, _, hfixed⟩ := exists_normalized_matrix A hshf hnt
  exact ⟨k, anchoredMatrix N, hk2, hk5, anchoredMatrix_isSHF N hN,
    anchoredMatrix_fixedRow N k hfixed, anchoredMatrix_anchorZero N⟩

end GPT6Astra

#print axioms GPT6Astra.exists_normalized_matrix
#print axioms GPT6Astra.shape_excludes_forbidden_mask
#print axioms GPT6Astra.exists_anchor_normalized_matrix
