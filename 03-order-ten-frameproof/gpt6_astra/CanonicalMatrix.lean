import MatrixNormalization
import DoubleLex

set_option autoImplicit false

namespace GPT6Astra

/-- Every nontrivial SHF of order ten has a representative in one of the four
fixed-weight, double-lex cases used by the direct finite calculation. -/
theorem exists_canonical_matrix (A : BinaryMatrix 10)
    (hshf : IsSHF A) (hnt : ¬ IsTrivial A) :
    ∃ (k : Nat) (B : BinaryMatrix 10),
      2 ≤ k ∧ k ≤ 5 ∧ IsSHF B ∧ Shape B k ∧ FixedRow B k ∧
      DoubleLexRows B ∧ DoubleLexColumns B k := by
  obtain ⟨k, N, hk2, hk5, hN, hshape, hfixed⟩ := exists_normalized_matrix A hshf hnt
  obtain ⟨q, p, hq, hp, hrows, hcols⟩ := exists_doubleLex_fixed N k hfixed
  exact ⟨k, permuteMatrix N q p, hk2, hk5, permuteMatrix_isSHF N hN q p,
    shape_permuteMatrix N k hshape q p,
    fixedRow_permuteMatrix N k hfixed q p hq hp, hrows, hcols⟩

/-- The anchored representative needs no row-weight restrictions after normalization. -/
theorem exists_anchored_canonical_matrix (A : BinaryMatrix 10)
    (hshf : IsSHF A) (hnt : ¬ IsTrivial A) :
    ∃ (k : Nat) (B : BinaryMatrix 10),
      2 ≤ k ∧ k ≤ 5 ∧ IsSHF B ∧ FixedRow B k ∧ AnchorZero B ∧
      DoubleLexRows B ∧ DoubleLexAnchoredColumns B k := by
  obtain ⟨k, N, hk2, hk5, hN, hfixed, hanchor⟩ :=
    exists_anchor_normalized_matrix A hshf hnt
  obtain ⟨q, p, hq, hp0, hp, hrows, hcols⟩ := exists_doubleLex_anchored_fixed N k hfixed
  exact ⟨k, permuteMatrix N q p, hk2, hk5, permuteMatrix_isSHF N hN q p,
    fixedRow_permuteMatrix N k hfixed q p hq hp,
    anchorZero_permuteMatrix N hanchor q p hq hp0, hrows, hcols⟩

end GPT6Astra

#print axioms GPT6Astra.exists_canonical_matrix
#print axioms GPT6Astra.exists_anchored_canonical_matrix
