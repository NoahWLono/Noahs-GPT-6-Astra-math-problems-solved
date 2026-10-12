import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Literal finite compositions of planar rotations, with their affine formula
and exact complex center coefficients. This is a semantic component of the
diameter-bound formalization, not the complete diameter theorem.
-/

namespace RotationComposition
noncomputable section

abbrev Step := ℝ × ℂ

def factor (angle : ℝ) : ℂ := Complex.exp ((angle : ℂ) * Complex.I)

def rotation (angle : ℝ) (center point : ℂ) : ℂ :=
  factor angle * point + (1 - factor angle) * center

def totalAngle : List Step → ℝ
  | [] => 0
  | s :: rest => s.1 + totalAngle rest

def applyRotations : List Step → ℂ → ℂ
  | [], point => point
  | s :: rest, point => applyRotations rest (rotation s.1 s.2 point)

def numerator : List Step → ℂ
  | [] => 0
  | s :: rest =>
      factor (totalAngle rest) * (1 - factor s.1) * s.2 + numerator rest

def weights : List Step → List ℂ
  | [] => []
  | s :: rest => factor (totalAngle rest) * (1 - factor s.1) :: weights rest

def center (steps : List Step) : ℂ :=
  numerator steps / (1 - factor (totalAngle steps))

theorem factor_zero : factor 0 = 1 := by simp [factor]

theorem factor_add (a b : ℝ) : factor (a + b) = factor a * factor b := by
  simp [factor, add_mul, Complex.exp_add]

theorem factor_norm (angle : ℝ) : ‖factor angle‖ = 1 := by
  simpa [factor] using Complex.norm_exp_ofReal_mul_I angle

theorem factor_ne_one {angle : ℝ} (hpos : 0 < angle) (hpi : angle ≤ Real.pi) :
    factor angle ≠ 1 := by
  intro h
  have hreal := congrArg Complex.re h
  have hcos : Real.cos angle = 1 := by
    simpa [factor, Complex.exp_ofReal_mul_I_re] using hreal
  have hlt : Real.cos angle < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hpi hpos
  linarith

theorem denominator_ne_zero {angle : ℝ} (hpos : 0 < angle)
    (hpi : angle ≤ Real.pi) : 1 - factor angle ≠ 0 := by
  intro h
  exact factor_ne_one hpos hpi (sub_eq_zero.mp h).symm

theorem rotation_fixes_center (angle : ℝ) (point : ℂ) :
    rotation angle point point = point := by
  dsimp [rotation]
  ring

theorem applyRotations_affine (steps : List Step) (point : ℂ) :
    applyRotations steps point =
      factor (totalAngle steps) * point + numerator steps := by
  induction steps generalizing point with
  | nil => simp [applyRotations, totalAngle, numerator, factor_zero]
  | cons s rest ih =>
      simp only [applyRotations, ih, totalAngle, numerator, factor_add, rotation]
      ring

theorem weights_length (steps : List Step) : (weights steps).length = steps.length := by
  induction steps with
  | nil => rfl
  | cons s rest ih => simp [weights, ih]

theorem weights_sum (steps : List Step) :
    (weights steps).sum = 1 - factor (totalAngle steps) := by
  induction steps with
  | nil => simp [weights, totalAngle, factor_zero]
  | cons s rest ih =>
      simp only [weights, List.sum_cons, ih, totalAngle, factor_add]
      ring

theorem numerator_eq_weighted_centers (steps : List Step) :
    numerator steps =
      (List.zipWith (fun w c : ℂ => w * c) (weights steps)
        (steps.map Prod.snd)).sum := by
  induction steps with
  | nil => rfl
  | cons s rest ih => simp [numerator, weights, ih]

theorem applyRotations_as_rotation (steps : List Step)
    (h : 1 - factor (totalAngle steps) ≠ 0) (point : ℂ) :
    applyRotations steps point = rotation (totalAngle steps) (center steps) point := by
  rw [applyRotations_affine]
  dsimp [rotation, center]
  field_simp [h]

theorem composite_fixed_iff (steps : List Step)
    (h : 1 - factor (totalAngle steps) ≠ 0) (point : ℂ) :
    applyRotations steps point = point ↔ point = center steps := by
  rw [applyRotations_affine]
  constructor
  · intro hp
    apply (eq_div_iff h).2
    linear_combination -hp
  · intro hp
    rw [hp]
    dsimp [center]
    field_simp [h]
    ring

theorem applyRotations_as_rotation_of_angle_bounds (steps : List Step)
    (hpos : 0 < totalAngle steps) (hpi : totalAngle steps ≤ Real.pi) (point : ℂ) :
    applyRotations steps point = rotation (totalAngle steps) (center steps) point :=
  applyRotations_as_rotation steps (denominator_ne_zero hpos hpi) point

#print axioms applyRotations_affine
#print axioms weights_sum
#print axioms applyRotations_as_rotation
#print axioms composite_fixed_iff

end
end RotationComposition
