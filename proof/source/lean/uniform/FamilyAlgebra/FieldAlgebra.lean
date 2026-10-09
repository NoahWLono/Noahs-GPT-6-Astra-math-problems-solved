import FamilyAlgebra.FamilyAlgebra
import Mathlib.Algebra.Field.Basic

namespace FamilyAlgebra
variable {E : Type*} [Field E]

def binarySum (weight : Nat → E) (bits : Nat → Bool) : Nat → E
  | 0 => 0
  | n+1 => binarySum weight bits n + if bits n then weight n else 0

/-- Frobenius preserves a binary linear combination in characteristic two. -/
theorem binarySum_square (two_zero : (2 : E) = 0)
    (weight : Nat → E) (bits : Nat → Bool) (n : Nat) :
    (binarySum weight bits n)^2 = binarySum (fun k => (weight k)^2) bits n := by
  induction n with
  | zero => simp [binarySum]
  | succ n ih =>
    simp only [binarySum, add_sq, two_zero, zero_mul, add_zero, ih]
    cases bits n <;> simp

/-- Independence of binary basis vectors implies independence of their squares.
The hypothesis is the explicit binary-sum form of linear independence. -/
theorem squared_basis_independent (two_zero : (2 : E) = 0)
    (weight : Nat → E) (n : Nat)
    (independent : ∀ bits, binarySum weight bits n = 0 ↔ ∀ k, k < n → bits k = false) :
    ∀ bits, binarySum (fun k => (weight k)^2) bits n = 0 ↔
      ∀ k, k < n → bits k = false := by
  intro bits
  rw [← binarySum_square two_zero, sq_eq_zero_iff, independent]

/-- General characteristic-two algebraic zero-locus criterion. The ordinary
binary basis is assumed independent; squared independence is proved above.
The expansion and triangular support remain explicit hypotheses. -/
theorem field_zero_locus (two_zero : (2 : E) = 0)
    (weight : Nat → E) (n : Nat) (positive : 0 < n)
    (independent : ∀ bits, binarySum weight bits n = 0 ↔ ∀ k, k < n → bits k = false)
    (active diag perturb : Nat → Bool) (value : E)
    (expansion : value = binarySum (fun k => (weight k)^2)
      (fun k => diag k ^^ perturb k) n)
    (bounded : ∀ j, n ≤ j → active j = false)
    (anisotropic : ∀ j, 0 < j → diag j = active j)
    (triangular : ∀ k, (∀ j, k < j → active j = false) → perturb k = false) :
    value = 0 ↔ diag 0 = false ∧ ∀ j, 0 < j → active j = false := by
  rw [expansion, squared_basis_independent two_zero weight n independent]
  constructor
  · intro hc
    have ha := triangular_elimination n active diag perturb bounded anisotropic triangular hc
    refine ⟨?_, ha⟩
    have hp := triangular 0 ha
    simpa [hp] using hc 0 positive
  · rintro ⟨h0, ha⟩ k _
    have hp : perturb k = false := triangular k (by
      intro j hj
      exact ha j (by omega))
    rw [hp, Bool.xor_false]
    by_cases hk : k = 0
    · simpa [hk] using h0
    · rw [anisotropic k (by omega)]
      exact ha k (by omega)

/-- A pair-indexed version: strict ordering and the midpoint identity give
triangularity automatically. The pairing must vanish if its upper parameter
vanishes. All these are explicit, checkable hypotheses. -/
theorem field_zero_locus_cross (two_zero : (2 : E) = 0)
    (weight : Nat → E) (n : Nat) (positive : 0 < n)
    (independent : ∀ bits, binarySum weight bits n = 0 ↔ ∀ k, k < n → bits k = false)
    (active diag : Nat → Bool) (B : Nat → Nat → Bool)
    (pairs : Nat → List (Nat × Nat)) (value : E)
    (ordered : ∀ k p, p ∈ pairs k → p.1 < p.2)
    (midpoint : ∀ k p, p ∈ pairs k → p.1 + p.2 = 2*k)
    (vanish : ∀ i j, active j = false → B i j = false)
    (expansion : value = binarySum (fun k => (weight k)^2)
      (fun k => diag k ^^ cross (pairs k) B) n)
    (bounded : ∀ j, n ≤ j → active j = false)
    (anisotropic : ∀ j, 0 < j → diag j = active j) :
    value = 0 ↔ diag 0 = false ∧ ∀ j, 0 < j → active j = false := by
  apply field_zero_locus two_zero weight n positive independent active diag
    (fun k => cross (pairs k) B) value expansion bounded anisotropic
  intro k ht
  apply cross_false_above (pairs k) B active k _ vanish ht
  intro p hp
  exact half_index_lt p.1 p.2 k (ordered k p hp) (midpoint k p hp)

#print axioms field_zero_locus_cross
#print axioms field_zero_locus
#print axioms squared_basis_independent
end FamilyAlgebra
