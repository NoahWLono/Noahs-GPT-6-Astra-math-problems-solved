import UniformRow
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace ProgressivePool
open Finset
variable {F I M : Type*} [Field F] [Fintype I] [Fintype M]

/-- Each stored coefficient is computed from the public matrix and private row. -/
def storedRow (A : I → M → F) (c : I → F) (j : M) : F := ∑ i, c i * A i j

def mvResidual (A : I → M → F) (sigma : M → F) (target : I → F) (i : I) : F :=
  (∑ j, A i j * sigma j) - target i

def storedCheck (A : I → M → F) (c : I → F) (sigma : M → F) (target : I → F) : F :=
  (∑ j, storedRow A c j * sigma j) - ∑ i, c i * target i

/-- Algebraic compiler correctness: stored checking is exactly testing a secret
row on the original verification residual, with no new assumption. -/
theorem storedCheck_eq (A : I → M → F) (c : I → F)
    (sigma : M → F) (target : I → F) :
    storedCheck A c sigma target = rowDot (mvResidual A sigma target) c := by
  simp only [storedCheck, storedRow, rowDot, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    mvResidual, mul_sub, sum_sub_distrib]
  congr 1
  simp_rw [sum_mul, mul_sum, mul_assoc]
  exact sum_comm

/-- Valid matrix equations pass every stored row. Auxiliary checks are separate. -/
theorem storedCheck_valid (A : I → M → F) (c : I → F)
    (sigma : M → F) (target : I → F)
    (h : mvResidual A sigma target = 0) : storedCheck A c sigma target = 0 := by
  rw [storedCheck_eq, h]
  simp [rowDot]

#print axioms storedCheck_eq
end ProgressivePool
