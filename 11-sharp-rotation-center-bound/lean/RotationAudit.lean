import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Exact audit of a planar-rotation claim. This is not a proof or disproof of
Duerer's conjecture, and is not a formalization of a polyhedral unfolding.
The rotation formula and the counterexample are elementary classical geometry.
-/

namespace RotationAudit

noncomputable section

abbrev Point := ℝ × ℝ

def rotation (angle : ℝ) (center point : Point) : Point :=
  (center.1 + Real.cos angle * (point.1 - center.1) -
      Real.sin angle * (point.2 - center.2),
   center.2 + Real.sin angle * (point.1 - center.1) +
      Real.cos angle * (point.2 - center.2))

theorem rotation_fixes_center (angle : ℝ) (center : Point) :
    rotation angle center center = center := by
  simp [rotation]

def quarterComposition (point : Point) : Point :=
  rotation (Real.pi / 2) (1, 0)
    (rotation (Real.pi / 2) (0, 0) point)

theorem quarterComposition_formula (point : Point) :
    quarterComposition point = (1 - point.1, -1 - point.2) := by
  ext <;> simp [quarterComposition, rotation] <;> ring

theorem quarter_angles_positive : 0 < Real.pi / 2 := by
  positivity

theorem quarter_angle_sum : Real.pi / 2 + Real.pi / 2 ≤ Real.pi := by
  linarith

theorem quarterComposition_fixed_iff (point : Point) :
    quarterComposition point = point ↔ point = (1 / 2, -1 / 2) := by
  rw [quarterComposition_formula]
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at hx hy ⊢ <;> linarith
  · rintro rfl
    norm_num

theorem quarterComposition_no_fixed_point_on_axis (x : ℝ) :
    quarterComposition (x, 0) ≠ (x, 0) := by
  intro h
  have h' := (quarterComposition_fixed_iff (x, 0)).mp h
  have hy := congrArg Prod.snd h'
  norm_num at hy

theorem segment_center_has_zero_second_coordinate (center : Point)
    (hc : center ∈ segment ℝ ((0, 0) : Point) (1, 0)) :
    center.2 = 0 := by
  rcases hc with ⟨a, b, ha, hb, hab, hcenter⟩
  rw [← hcenter]
  simp

theorem no_rotation_with_segment_center :
    ¬ ∃ (angle : ℝ) (center : Point),
      center ∈ segment ℝ ((0, 0) : Point) (1, 0) ∧
      ∀ point, quarterComposition point = rotation angle center point := by
  rintro ⟨angle, center, hc, heq⟩
  have hy := segment_center_has_zero_second_coordinate center hc
  have hfix : quarterComposition center = center := by
    rw [heq center, rotation_fixes_center]
  have hcenter := (quarterComposition_fixed_iff center).mp hfix
  have hcoord := congrArg Prod.snd hcenter
  dsimp at hcoord
  linarith

/- A second exact witness uses a first-quadrant rotation with cosine 3/5
and sine 4/5. Its angle is strictly below pi/2, so two such angles sum to
strictly less than pi. The following lemmas certify the algebraic part;
they deliberately do not claim a Lean proof of that angle interpretation. -/

def rationalTurn (center point : Point) : Point :=
  (center.1 + (3 / 5 : ℝ) * (point.1 - center.1) -
      (4 / 5 : ℝ) * (point.2 - center.2),
   center.2 + (4 / 5 : ℝ) * (point.1 - center.1) +
      (3 / 5 : ℝ) * (point.2 - center.2))

def rationalComposition (point : Point) : Point :=
  rationalTurn (1, 0) (rationalTurn (0, 0) point)

theorem rational_coefficients_unit :
    (3 / 5 : ℝ)^2 + (4 / 5 : ℝ)^2 = 1 := by norm_num

theorem rational_coefficients_positive :
    0 < (3 / 5 : ℝ) ∧ 0 < (4 / 5 : ℝ) := by norm_num

theorem rationalTurn_preserves_squared_distance (center point : Point) :
    ((rationalTurn center point).1 - center.1)^2 +
      ((rationalTurn center point).2 - center.2)^2 =
    (point.1 - center.1)^2 + (point.2 - center.2)^2 := by
  dsimp [rationalTurn]
  ring

theorem rationalComposition_fixed_iff (point : Point) :
    rationalComposition point = point ↔ point = (1 / 2, -1 / 4) := by
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    dsimp [rationalComposition, rationalTurn] at hx hy
    apply Prod.ext <;> dsimp <;> linarith
  · rintro rfl
    norm_num [rationalComposition, rationalTurn]

theorem rationalComposition_no_fixed_point_on_axis (x : ℝ) :
    rationalComposition (x, 0) ≠ (x, 0) := by
  intro h
  have h' := (rationalComposition_fixed_iff (x, 0)).mp h
  have hy := congrArg Prod.snd h'
  norm_num at hy

#print axioms no_rotation_with_segment_center
#print axioms rationalComposition_fixed_iff

end
end RotationAudit
