import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.CharP.Two
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PfaffianEight
abbrev F := ZMod 2
private theorem sub_2_0 (A : Matrix (Fin 2) (Fin 2) F) :
 A.submatrix Fin.succ (Fin.succAbove (0 : Fin 2)) = !![A 1 1] := by
 ext i j
 fin_cases i <;> fin_cases j <;> rfl

private theorem sub_2_1 (A : Matrix (Fin 2) (Fin 2) F) :
 A.submatrix Fin.succ (Fin.succAbove (1 : Fin 2)) = !![A 1 0] := by
 ext i j
 fin_cases i <;> fin_cases j <;> rfl

theorem laplace2 (A : Matrix (Fin 2) (Fin 2) F) :
 A.det = A 0 0 * Matrix.det !![A 1 1] +
 A 0 1 * Matrix.det !![A 1 0] := by
 rw [Matrix.det_succ_row_zero]
 simp only [Fin.sum_univ_succ, show (-1:F)=1 by decide, one_pow, one_mul, Fin.sum_univ_zero, add_zero]
 simp only [show (0 : Fin 1).succ = (1 : Fin 2) by rfl]
 simp only [sub_2_0, sub_2_1]
 try simp only [add_assoc]
 try rfl

end PfaffianEight
