import FamilyAlgebra.ComponentCount
import QuadraticWalshFamily

namespace FamilyAlgebra
open FastWalsh QuadraticWalshMatrix

/-- A fully assembled uniform existence theorem for the actual vectorial
quadratic and actual finite Walsh definitions. Every positive e produces one
map F2^(4e)→F2^(4e) with exactly 3*2^(2e-1)-1 nonzero nonbent components.

No algebraic/trace/coordinate/polarization/counting bridge is assumed here.
This is an existence/count theorem, not a global sharpness or novelty claim. -/
theorem uniform_quadratic_family (e : Nat) (positive : 0<e) :
    ∃ cs : List (Nat × Nat × BitVec (4*e)),
      (∀ b : BitVec (4*e), IsBent (quadratic cs : BitVec (4*e) → BitVec (4*e)) b ↔
        ¬badFullMask e positive (coords b)) ∧
      Nat.card {b : BitVec (4*e) //
        ¬IsBent (quadratic cs : BitVec (4*e) → BitVec (4*e)) b ∧ b≠0} =
          3*2^(2*e-1)-1 := by
  classical
  obtain ⟨a,ha⟩ := galois_power_basis e positive
  let L := fullLinearFamily e positive a
  let cs := QuadraticWalshFamily.familyCoefficients L
  have hAlt : ∀ t v, L t v v=0 := fun t => fullLinearFamily_alt e positive a t
  have hclass : ∀ b : BitVec (4*e), IsBent (quadratic cs : BitVec (4*e) → BitVec (4*e)) b ↔
      ¬badFullMask e positive (coords b) := by
    intro b
    rw [QuadraticWalshFamily.family_bent_iff L hAlt b]
    exact fullLinearFamily_nondegenerate_iff e positive a ha (coords b)
  exact ⟨cs, hclass, nonzero_nonbent_card_of_classification e positive (quadratic cs) hclass⟩

theorem uniform_nonbent_count (e : Nat) (positive : 0<e) :
    ∃ cs : List (Nat × Nat × BitVec (4*e)),
      Nat.card {b : BitVec (4*e) //
        ¬IsBent (quadratic cs : BitVec (4*e) → BitVec (4*e)) b ∧ b≠0} =
          3*2^(2*e-1)-1 := by
  obtain ⟨cs,_,h⟩ := uniform_quadratic_family e positive
  exact ⟨cs,h⟩

theorem uniform_twelve_count :
    ∃ cs : List (Nat × Nat × BitVec 12),
      Nat.card {b : BitVec 12 // ¬IsBent (quadratic cs : BitVec 12 → BitVec 12) b ∧ b≠0}=95 :=
  uniform_nonbent_count 3 (by decide)

#print axioms uniform_quadratic_family
#print axioms uniform_nonbent_count
#print axioms uniform_twelve_count
end FamilyAlgebra
