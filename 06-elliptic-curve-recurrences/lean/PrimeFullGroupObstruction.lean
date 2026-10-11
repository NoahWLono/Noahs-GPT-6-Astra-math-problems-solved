import EllipticHasseOdd
import CyclicFieldTheorem
import PrimeFieldArithmetic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! T5 for the actual full elliptic group over F_p. The only geometric input
is the locally proved Hasse bound; no Hasse or subgroup-order assumption is supplied.
The Möbius transformation is represented by an arbitrary invertible 2×2 matrix. -/
namespace Astra01
noncomputable section
open WeierstrassCurve.Affine
open scoped MatrixGroups LinearAlgebra.Projectivization
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq (ZMod p) := Classical.decEq _
local instance : MulAction (GL (Fin 2) (ZMod p)) (ℙ (ZMod p) (Plane (ZMod p))) :=
  projectiveMatrixAction

/-- Every full base-field Möbius recurrence along a nonzero translation is constant
when p≥17 and the full elliptic group has prime cardinality different from p. -/
theorem prime_full_group_recurrence_constant
    (hp17 : 17 ≤ p) (W : WeierstrassCurve.Affine (ZMod p)) [W.IsElliptic]
    (n : ℕ) (hn : n.Prime) (hcard : Nat.card W.Point = n) (hnp : n ≠ p)
    (G : W.Point) (hG : G ≠ 0)
    (f : W.Point → ℙ (ZMod p) (Plane (ZMod p))) (M : GL (Fin 2) (ZMod p))
    (hrec : ∀ P, f (P+G) = M • f P) : ∀ P, f P = f 0 := by
  letI : Fact n.Prime := ⟨hn⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hlower : p+1 < 2*n := by
    have h := EllipticFrobenius.half_field_card_lt_point_count W hchar
      (by simpa only [ZMod.card] using hp17)
    simpa only [ZMod.card,hcard] using h
  have hn3 : 3 ≤ n := by omega
  have hmem (P : W.Point) : P ∈ AddSubgroup.zmultiples G :=
    mem_zmultiples_of_prime_card hcard hG
  have horder : addOrderOf G = n :=
    (addOrderOf_eq_card_of_forall_mem_zmultiples hmem).trans hcard
  intro P
  by_contra hnon
  have h := cyclic_subgroup_projective_recurrence (F := ZMod p) G f M n hn hn3 horder
    (fun Q _ => hrec Q) ⟨P,hmem P,hnon⟩
  have halt : n = p ∨ n ∣ p-1 ∨ n ∣ p+1 := by
    simpa only [ZMod.ringChar_zmod_n,ZMod.card,Module.finrank_self,pow_one] using h.2.2.1
  have he := prime_field_divisibility_excluded p n Fact.out hn hp17 hlower
  rcases halt with h | h | h
  · exact hnp h
  · exact he.1 h
  · exact he.2 h

end
end Astra01
#print axioms Astra01.prime_full_group_recurrence_constant
