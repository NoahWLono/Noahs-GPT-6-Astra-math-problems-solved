import FiniteFieldAction
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! The genuine matrix action on P¹(K), using mathlib's quotient of nonzero
vectors by nonzero scalar multiplication. This avoids any finite-table model.
The representative matrix is explicit; no claim of exact projective order is made. -/
namespace Astra01
noncomputable section
open scoped MatrixGroups LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

/-- The natural action induced by an invertible 2×2 matrix on projective lines. -/
@[implicit_reducible] def projectiveMatrixAction : MulAction (GL (Fin 2) K) (ℙ K (Fin 2 → K)) where
  smul M z := z.map (Matrix.GeneralLinearGroup.toLin M : (Fin 2 → K) →ₗ[K] (Fin 2 → K))
    (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv.injective
  one_smul z := by
    change Projectivization.map _ _ z = z
    simp only [map_one, Units.val_one, Module.End.one_eq_id, Projectivization.map_id,
      id_eq]
  mul_smul M N z := by
    change Projectivization.map _ _ z = Projectivization.map _ _ (Projectivization.map _ _ z)
    simp only [map_mul, Units.val_mul, Module.End.mul_eq_comp]
    exact congrFun (Projectivization.map_comp
      (Matrix.GeneralLinearGroup.toLin N : (Fin 2 → K) →ₗ[K] (Fin 2 → K))
      (Matrix.GeneralLinearGroup.toLin N).toLinearEquiv.injective
      (Matrix.GeneralLinearGroup.toLin M : (Fin 2 → K) →ₗ[K] (Fin 2 → K))
      (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv.injective) z

local instance : MulAction (GL (Fin 2) K) (ℙ K (Fin 2 → K)) := projectiveMatrixAction

/-- Necessary field alternatives for a nonfixed prime-period point of an
actual projective-line matrix transformation. -/
theorem projective_prime_period_field_alternatives [Fintype K]
    (M : GL (Fin 2) K) (x : ℙ K (Fin 2 → K)) (n : ℕ) (hn : n.Prime)
    (hcycle : M^n • x = x) (hnotfixed : M • x ≠ x) :
    n = ringChar K ∨ n ∣ Fintype.card K - 1 ∨ n ∣ Fintype.card K + 1 :=
  prime_period_gl2_field_alternatives M x n hn hcycle hnotfixed

/-- The paper's necessary field alternatives for a full nonconstant prime
cyclic recurrence on the genuine projective line, with an explicit matrix. -/
theorem projective_prime_recurrence_field_alternatives [Fintype K]
    (M : GL (Fin 2) K) (z : ℕ → ℙ K (Fin 2 → K)) (n : ℕ) (hn : n.Prime)
    (hstep : ∀ i < n, z (i+1) = M • z i)
    (hclose : z n = z 0) (hnonconstant : ∃ i < n, z i ≠ z 0) :
    n = ringChar K ∨ n ∣ Fintype.card K - 1 ∨ n ∣ Fintype.card K + 1 :=
  prime_recurrence_gl2_field_alternatives M z n hn hstep hclose hnonconstant

#print axioms projective_prime_recurrence_field_alternatives
#print axioms projectiveMatrixAction
#print axioms projective_prime_period_field_alternatives
end
end Astra01
