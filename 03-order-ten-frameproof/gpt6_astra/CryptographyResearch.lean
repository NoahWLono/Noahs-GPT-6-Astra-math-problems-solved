import Mathlib.Data.Fintype.Basic

/-!
# GPT-6 Astra: a formal specification of the order-ten frameproof-code problem

This file does NOT prove or refute `OpenProblem10`.  The proved statements below
are specification checks and elementary background facts; no novelty is claimed.
The source problem is Guo--Stinson--van Trung, "On symmetric designs and binary
3-frameproof codes", concluding open problem 3 (2015).
-/

namespace GPT6Astra

abbrev BinaryMatrix (n : Nat) := Fin n → Fin n → Bool

/-- One row distinguishes the designated column from each of three others. -/
def Separates {n : Nat} (A : BinaryMatrix n) (r a b c d : Fin n) : Prop :=
  A r a ≠ A r b ∧ A r a ≠ A r c ∧ A r a ≠ A r d

/-- Matrix form of an SHF(n; n, 2, {1,3}). -/
def IsSHF {n : Nat} (A : BinaryMatrix n) : Prop :=
  ∀ a b c d : Fin n,
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∃ r : Fin n, Separates A r a b c d

def identityMatrix (n : Nat) : BinaryMatrix n :=
  fun r c => decide (r = c)

/-- A permutation matrix, allowing independent complementation of its rows.
    A permutation of columns is absorbed in the equivalence `p`. -/
def IsTrivial {n : Nat} (A : BinaryMatrix n) : Prop :=
  ∃ (p : Fin n ≃ Fin n) (flip : Fin n → Bool),
    ∀ r c, A r c = Bool.xor (decide (p r = c)) (flip r)

/-- The existential open question, recorded as a definition, not an axiom. -/
def OpenProblem10 : Prop :=
  ∃ A : BinaryMatrix 10, IsSHF A ∧ ¬ IsTrivial A

theorem identity_isSHF (n : Nat) : IsSHF (identityMatrix n) := by
  intro a b c d hab hac had _ _ _
  refine ⟨a, ?_⟩
  simp [Separates, identityMatrix, hab, hac, had]

theorem identity_isTrivial (n : Nat) : IsTrivial (identityMatrix n) := by
  refine ⟨Equiv.refl _, fun _ => false, ?_⟩
  intro r c
  simp [identityMatrix]
  rfl

def complementRows {n : Nat} (A : BinaryMatrix n)
    (flip : Fin n → Bool) : BinaryMatrix n :=
  fun r c => Bool.xor (A r c) (flip r)

theorem xor_ne_xor_right (x y bit : Bool) :
    Bool.xor x bit ≠ Bool.xor y bit ↔ x ≠ y := by
  cases x <;> cases y <;> cases bit <;> decide

theorem separates_complementRows_iff {n : Nat} (A : BinaryMatrix n)
    (flip : Fin n → Bool) (r a b c d : Fin n) :
    Separates (complementRows A flip) r a b c d ↔ Separates A r a b c d := by
  simp only [Separates, complementRows, xor_ne_xor_right]

theorem isSHF_complementRows_iff {n : Nat} (A : BinaryMatrix n)
    (flip : Fin n → Bool) :
    IsSHF (complementRows A flip) ↔ IsSHF A := by
  simp only [IsSHF, separates_complementRows_iff]

/-- If a coalition can copy its members' bits coordinate by coordinate to
    reproduce another column, it cannot be separated from that column. -/
theorem separation_iff_no_descendant {n : Nat} (A : BinaryMatrix n)
    (a b c d : Fin n) :
    (∃ r, Separates A r a b c d) ↔
      ¬ (∀ r, A r a = A r b ∨ A r a = A r c ∨ A r a = A r d) := by
  simp only [Separates]
  classical
  simp only [not_forall, not_or]

end GPT6Astra

#print GPT6Astra.OpenProblem10
#print axioms GPT6Astra.identity_isSHF
#print axioms GPT6Astra.identity_isTrivial
#print axioms GPT6Astra.isSHF_complementRows_iff
#print axioms GPT6Astra.separation_iff_no_descendant
