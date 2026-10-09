import MatchingIndicator
import Mathlib.LinearAlgebra.Matrix.BilinearForm
set_option maxRecDepth 1024
set_option maxHeartbeats 500000
namespace MatchingDeterminant
open LinearMap
abbrev Form8 := LinearMap.BilinForm F Vec8

def formMatrix (B : Form8) : Mat8 := fun i j => B (Pi.single i 1) (Pi.single j 1)

def matrixPencil (L : Vec8 →ₗ[F] Form8) : Vec8 →ₗ[F] Mat8 where
  toFun b := formMatrix (L b)
  map_add' b c := by
    ext i j
    simp [formMatrix]
  map_smul' c b := by
    ext i j
    simp [formMatrix]

@[simp] theorem matrixPencil_apply (L : Vec8 →ₗ[F] Form8) (b : Vec8) (i j : Fin 8) :
    matrixPencil L b i j = L b (Pi.single i 1) (Pi.single j 1) := rfl

theorem symmetric_of_alternating (B : Form8) (h : ∀ x, B x x = 0) (x y : Vec8) :
    B x y = B y x := by
  have hh := h (x+y)
  simp only [map_add, LinearMap.add_apply, h, zero_add, add_zero] at hh
  exact ((eq_neg_iff_add_eq_zero.mpr hh).trans (CharTwo.neg_eq _)).symm

def formNonsingularIndicator (B : Form8) : F :=
  PfaffianEight.nonsingularIndicator (formMatrix B)

theorem form_indicator_one_iff (B : Form8) :
    formNonsingularIndicator B = 1 ↔ B.Nondegenerate := by
  unfold formNonsingularIndicator
  rw [PfaffianEight.indicator_one_iff]
  have hm : formMatrix B = LinearMap.BilinForm.toMatrix' B := rfl
  rw [hm]
  exact LinearMap.BilinForm.nondegenerate_toMatrix'_iff

/-- Actual nondegeneracy indicator for a linear pencil of alternating
bilinear forms on the eight-dimensional binary vector space. -/
theorem degree_form_nonsingular_indicator (L : Vec8 →ₗ[F] Form8)
    (h : ∀ b x, L b x x = 0) :
    BooleanANF.HasDegreeLE (fun b => formNonsingularIndicator (L b)) 4 := by
  change BooleanANF.HasDegreeLE (fun b => nonsingularIndicator (matrixPencil L b)) 4
  apply degree_nonsingular_indicator
  · intro b i j
    simp only [matrixPencil_apply]
    exact symmetric_of_alternating (L b) (h b) _ _
  · intro b i
    simp only [matrixPencil_apply]
    exact h b _

theorem degree_form_singular_indicator (L : Vec8 →ₗ[F] Form8)
    (h : ∀ b x, L b x x = 0) :
    BooleanANF.HasDegreeLE (fun b => 1 + formNonsingularIndicator (L b)) 4 := by
  exact ((BooleanANF.degree_const 1).mono (by omega)).add
    (degree_form_nonsingular_indicator L h)

#print axioms degree_form_nonsingular_indicator
#print axioms form_indicator_one_iff
end MatchingDeterminant
