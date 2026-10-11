import ProjectiveOrder
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-! The actual PGL quotient action on the genuine projective line. -/
namespace Astra01
noncomputable section
open scoped MatrixGroups LinearAlgebra.Projectivization
variable {K : Type*} [Field K]
local instance : MulAction (GL (Fin 2) K) (ℙ K (Plane K)) := projectiveMatrixAction

theorem scalar_projective_action (u : Kˣ) (x : ℙ K (Plane K)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u • x = x := by
  change Projectivization.map _ _ x = x
  rw [← Projectivization.mk_rep x,Projectivization.map_mk,Projectivization.mk_eq_mk_iff']
  refine ⟨(u : K),?_⟩
  ext i
  fin_cases i <;> simp [Matrix.GeneralLinearGroup.toLin_apply,Matrix.mulVecLin_apply,
    Matrix.GeneralLinearGroup.coe_scalar,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.scalar]

@[implicit_reducible] def projectiveQuotientAction : MulAction (PGL(2,K)) (ℙ K (Plane K)) :=
  Matrix.ProjGenLinGroup.mulActionOfGL scalar_projective_action

local instance : MulAction (PGL(2,K)) (ℙ K (Plane K)) := projectiveQuotientAction

theorem pgl_mk_smul (M : GL (Fin 2) K) (x : ℙ K (Plane K)) :
    Matrix.ProjGenLinGroup.mk M • x = M • x := rfl

theorem pgl_eq_one_of_three_fixed (M : GL (Fin 2) K) (x y z : ℙ K (Plane K))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : M • x = x) (hy : M • y = y) (hz : M • z = z) :
    Matrix.ProjGenLinGroup.mk M = 1 := by
  let F : Module.End K (Plane K) := Matrix.GeneralLinearGroup.toLin M
  have hF : Function.Injective F := (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv.injective
  obtain ⟨a,ha⟩ := scalar_of_three_projective_fixed F hF x y z hxy hxz hyz hx hy hz
  rw [Matrix.ProjGenLinGroup.mk_eq_one,Subgroup.mem_center_iff]
  intro N
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply Units.ext
  simp only [map_mul, Units.val_mul]
  change (Matrix.GeneralLinearGroup.toLin N : Module.End K (Plane K))*F =
    F*(Matrix.GeneralLinearGroup.toLin N : Module.End K (Plane K))
  rw [ha]
  ext w
  simp [Module.End.mul_apply]

end
end Astra01
#print axioms Astra01.projectiveQuotientAction
#print axioms Astra01.pgl_eq_one_of_three_fixed
