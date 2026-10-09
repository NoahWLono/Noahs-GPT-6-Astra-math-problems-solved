import FamilyAlgebra.ParameterLinearity
import FamilyMaskCount.MaskCount
import QuadraticWalshMatrix

namespace FamilyAlgebra
open FastWalsh QuadraticWalshMatrix

/-- Transfer the exact canonical mask count through the proved BitVec/F2
coordinate equivalence, for an actual vectorial Boolean function. -/
noncomputable def nonbentMaskEquiv (n : Nat) (positive : 0<n)
    (f : BitVec (4*n) → BitVec (4*n))
    (classification : ∀ b, IsBent f b ↔ ¬badFullMask n positive (coords b)) :
    {b : BitVec (4*n) // ¬IsBent f b ∧ b≠0} ≃
      {v : Fin (4*n) → ZMod 2 // badFullMask n positive v ∧ v≠0} where
  toFun b := ⟨coords b.val, by
    constructor
    · have h := b.property.1
      rw [classification] at h
      exact Classical.not_not.mp h
    · intro h
      apply b.property.2
      apply coords_injective
      rw [h, coords_zero]⟩
  invFun v := ⟨decode v.val, by
    constructor
    · rw [classification, coords_decode]
      exact not_not.mpr v.property.1
    · intro h
      apply v.property.2
      rw [← coords_decode v.val, h, coords_zero]⟩
  left_inv b := by apply Subtype.ext; exact decode_coords b.val
  right_inv v := by apply Subtype.ext; exact coords_decode v.val

theorem nonzero_nonbent_card_of_classification (n : Nat) (positive : 0<n)
    (f : BitVec (4*n) → BitVec (4*n))
    (classification : ∀ b, IsBent f b ↔ ¬badFullMask n positive (coords b)) :
    Nat.card {b : BitVec (4*n) // ¬IsBent f b ∧ b≠0} = 3*2^(2*n-1)-1 := by
  rw [Nat.card_congr (nonbentMaskEquiv n positive f classification), Nat.card_eq_fintype_card]
  exact FamilyMaskCount.nonzero_badFullMask_card n positive

#print axioms nonzero_nonbent_card_of_classification
end FamilyAlgebra
