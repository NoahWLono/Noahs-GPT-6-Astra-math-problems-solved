import Mathlib.Algebra.Field.ZMod
import PfaffianDegree
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
namespace PfaffianEight
/-- The arbitrary alternating binary matrix, parameterized by its 28 upper entries. -/
def alternatingMatrix (a : Fin 28 → F) : Mat :=
  !![(0:F),a 0,a 1,a 2,a 3,a 4,a 5,a 6; a 0,(0:F),a 7,a 8,a 9,a 10,a 11,a 12; a 1,a 7,(0:F),a 13,a 14,a 15,a 16,a 17; a 2,a 8,a 13,(0:F),a 18,a 19,a 20,a 21; a 3,a 9,a 14,a 18,(0:F),a 22,a 23,a 24; a 4,a 10,a 15,a 19,a 22,(0:F),a 25,a 26; a 5,a 11,a 16,a 20,a 23,a 25,(0:F),a 27; a 6,a 12,a 17,a 21,a 24,a 26,a 27,(0:F)]

def upperCoordinates (M : Mat) : Fin 28 → F :=
  ![M 0 1,M 0 2,M 0 3,M 0 4,M 0 5,M 0 6,M 0 7,M 1 2,M 1 3,M 1 4,M 1 5,M 1 6,M 1 7,M 2 3,M 2 4,M 2 5,M 2 6,M 2 7,M 3 4,M 3 5,M 3 6,M 3 7,M 4 5,M 4 6,M 4 7,M 5 6,M 5 7,M 6 7]

def IsAlternating (M : Mat) : Prop :=
  (∀ i, M i i = 0) ∧ (∀ i j, M i j = M j i)

theorem alternatingMatrix_coordinates (M : Mat) (h : IsAlternating M) :
    alternatingMatrix (upperCoordinates M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [alternatingMatrix, upperCoordinates, Matrix.of_apply, Matrix.cons_val] <;>
    first | rfl | exact (h.1 _).symm | exact h.2 _ _

theorem binary_zero_or_one (a : F) : a = 0 ∨ a = 1 := by
  have h : ∀ a : F, a = 0 ∨ a = 1 := by decide
  exact h a

theorem square_eq_self (a : F) : a ^ 2 = a := by
  rcases binary_zero_or_one a with rfl | rfl <;> decide

theorem one_iff_nonzero (a : F) : a = 1 ↔ a ≠ 0 := by
  rcases binary_zero_or_one a with rfl | rfl <;> decide

/-- A binary-valued indicator of matrix nonsingularity. -/
def nonsingularIndicator (M : Mat) : F := if M.det = 0 then 0 else 1

theorem indicator_one_iff (M : Mat) :
    nonsingularIndicator M = 1 ↔ Matrix.Nondegenerate M := by
  rw [Matrix.nondegenerate_iff_det_ne_zero]
  simp [nonsingularIndicator]

theorem indicator_eq_det (M : Mat) : nonsingularIndicator M = M.det := by
  rcases binary_zero_or_one M.det with h | h <;> simp [nonsingularIndicator, h]

#print axioms alternatingMatrix_coordinates
#print axioms indicator_one_iff
end PfaffianEight
