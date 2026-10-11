import ProjectiveFieldCondition
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! An actual projective-line fixed-point theorem over an algebraically
closed field, used in the analytic T1 proof. It does not assert that an
arbitrary degree-one rational morphism has already been represented by a matrix. -/
namespace Astra01
noncomputable section
open scoped MatrixGroups LinearAlgebra.Projectivization
variable {K : Type*} [Field K] [IsAlgClosed K]
local instance : MulAction (GL (Fin 2) K) (ℙ K (Fin 2 → K)) := projectiveMatrixAction

/-- Every invertible 2×2 matrix over an algebraically closed field has a
fixed point on the genuine projective line, in arbitrary characteristic. -/
theorem projective_transformation_has_fixed_point (M : GL (Fin 2) K) :
    ∃ x : ℙ K (Fin 2 → K), M • x = x := by
  let F : Module.End K (Fin 2 → K) := Matrix.GeneralLinearGroup.toLin M
  obtain ⟨a,ha⟩ := F.exists_eigenvalue
  obtain ⟨v,hv⟩ := ha.exists_hasEigenvector
  refine ⟨Projectivization.mk K v hv.2, ?_⟩
  change Projectivization.map F _ (Projectivization.mk K v hv.2) =
    Projectivization.mk K v hv.2
  rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨a,hv.apply_eq_smul.symm⟩

#print axioms projective_transformation_has_fixed_point
end
end Astra01
