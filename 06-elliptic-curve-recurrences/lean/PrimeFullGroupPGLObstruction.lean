import PrimeFullGroupObstruction
import ProjectiveQuotientAction

/-! The literal PGL quotient formulation of T5. Representative existence follows
from the actual quotient projection, rather than being an extra hypothesis. -/
namespace Astra01
noncomputable section
open WeierstrassCurve.Affine
open scoped MatrixGroups LinearAlgebra.Projectivization
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq (ZMod p) := Classical.decEq _
local instance : MulAction (GL (Fin 2) (ZMod p)) (ℙ (ZMod p) (Plane (ZMod p))) :=
  projectiveMatrixAction
local instance : MulAction (PGL(2,ZMod p)) (ℙ (ZMod p) (Plane (ZMod p))) :=
  projectiveQuotientAction

theorem prime_full_group_pgl_recurrence_constant
    (hp17 : 17 ≤ p) (W : WeierstrassCurve.Affine (ZMod p)) [W.IsElliptic]
    (n : ℕ) (hn : n.Prime) (hcard : Nat.card W.Point = n) (hnp : n ≠ p)
    (G : W.Point) (hG : G ≠ 0)
    (f : W.Point → ℙ (ZMod p) (Plane (ZMod p))) (M : PGL(2,ZMod p))
    (hrec : ∀ P, f (P+G) = M • f P) : ∀ P, f P = f 0 := by
  obtain ⟨A,rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective M
  simp only [pgl_mk_smul] at hrec
  exact prime_full_group_recurrence_constant p hp17 W n hn hcard hnp G hG f A hrec

end
end Astra01
#print axioms Astra01.prime_full_group_pgl_recurrence_constant
