import RotationSharpness

/-! A semantic fixture using the alternate literal formula exp(i angle)*(z-center)+center.
This is a project-authored fixture, not an independent third-party proof review. -/
namespace RotationExpectedStatement
noncomputable section
open RotationComposition RotationCenterBound

def applyLiteral : List (ℝ × ℂ) → ℂ → ℂ
  | [], z => z
  | s :: rest, z => applyLiteral rest
      (Complex.exp ((s.1 : ℂ) * Complex.I) * (z - s.2) + s.2)

theorem literal_eq (steps : List (ℝ × ℂ)) (z : ℂ) :
    applyLiteral steps z = applyRotations steps z := by
  induction steps generalizing z with
  | nil => rfl
  | cons s rest ih =>
      simp only [applyLiteral, applyRotations, ih]
      congr 1
      simp only [rotation, factor]
      ring

theorem total_eq_sum (steps : List (ℝ × ℂ)) :
    totalAngle steps = (steps.map Prod.fst).sum := by
  induction steps with
  | nil => rfl
  | cons s rest ih => simp [totalAngle, ih]

theorem literal_composite_center_bound (steps : List (ℝ × ℂ))
    (hω : ∀ s ∈ steps, 0 ≤ s.1)
    (hpos : 0 < (steps.map Prod.fst).sum)
    (hpi : (steps.map Prod.fst).sum ≤ Real.pi)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ s ∈ steps, ∀ t ∈ steps, ‖s.2 - t.2‖ ≤ D) :
    ∃ c : ℂ,
      (∀ z, applyLiteral steps z =
        Complex.exp (((steps.map Prod.fst).sum : ℂ) * Complex.I) * (z - c) + c) ∧
      (∀ z, applyLiteral steps z = z ↔ z = c) ∧
      ∃ w ∈ convexHull ℝ {z : ℂ | z ∈ steps.map Prod.snd},
        ‖c - w‖ ≤ (D / 2) * Real.tan ((steps.map Prod.fst).sum / 4) := by
  obtain ⟨c, hc, hfix, w, hw, hb⟩ := composite_rotation_center_near_hull steps hω
    (by simpa only [total_eq_sum] using hpos)
    (by simpa only [total_eq_sum] using hpi) D hD hdiam
  refine ⟨c, ?_, ?_, w, hw, ?_⟩
  · intro z
    rw [literal_eq, hc]
    simp only [rotation, factor, total_eq_sum]
    ring
  · intro z
    rw [literal_eq]
    exact hfix z
  · simpa only [total_eq_sum] using hb

#print axioms literal_composite_center_bound
#print axioms RotationSharpness.sharpness
end
end RotationExpectedStatement
