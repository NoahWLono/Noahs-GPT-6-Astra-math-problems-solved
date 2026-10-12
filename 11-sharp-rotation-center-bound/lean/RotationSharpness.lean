import RotationCenterBound

namespace RotationSharpness
noncomputable section
open RotationComposition RotationCoefficients RotationCenterBound

def twoSteps (A D : ℝ) : List Step := [(A / 2, 0), (A / 2, (D : ℂ))]

theorem twoSteps_total (A D : ℝ) : totalAngle (twoSteps A D) = A := by
  simp only [twoSteps, totalAngle]
  ring

theorem twoSteps_nonneg {A D : ℝ} (hA : 0 ≤ A) :
    ∀ s ∈ twoSteps A D, 0 ≤ s.1 := by
  intro s hs
  simp only [twoSteps, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> dsimp <;> linarith

theorem twoSteps_pairwise {A D : ℝ} (hD : 0 ≤ D) :
    ∀ s ∈ twoSteps A D, ∀ t ∈ twoSteps A D, ‖s.2 - t.2‖ ≤ D := by
  intro s hs t ht
  simp only [twoSteps, List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD, hD]

theorem endpoints_distance {D : ℝ} (hD : 0 ≤ D) : ‖(D : ℂ) - 0‖ = D := by
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hD]

theorem center_twoSteps_im {A D : ℝ} (hA : 0 < A) (hpi : A ≤ Real.pi) :
    (center (twoSteps A D)).im = -((D / 2) * Real.tan (A / 4)) := by
  have hs : Real.sin (A / 2) ≠ 0 := (half_sin_pos hA hpi).ne'
  have hden := denominator_ne_zero hA hpi
  have hcenter : coeff A 0 (A / 2) * (D : ℂ) = center (twoSteps A D) := by
    unfold center
    rw [twoSteps_total]
    apply (eq_div_iff hden).2
    have hp := weighted_product_sum A (twoSteps A D) hs
    simpa only [twoSteps, weighted, totalAngle, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, mul_zero, zero_mul, zero_add, add_zero, mul_comm] using hp
  have hcoeff : (coeff A 0 (A / 2)).im = -(Real.tan (A / 4) / 2) := by
    change (Real.cos (0 - A / 2) - Real.cos (0 + A / 2 - A / 2)) /
      (2 * Real.sin (A / 2)) = _
    simp only [zero_sub, zero_add, sub_self, Real.cos_neg, Real.cos_zero]
    calc
      (Real.cos (A / 2) - 1) / (2 * Real.sin (A / 2)) =
          -((1 - Real.cos (A / 2)) / (2 * Real.sin (A / 2))) := by ring
      _ = _ := by rw [half_angle_ratio hA hpi]
  rw [← hcenter, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_add, hcoeff]
  ring

theorem twoSteps_hull_im_zero (A D : ℝ) {w : ℂ}
    (hw : w ∈ convexHull ℝ (centers (twoSteps A D))) : w.im = 0 := by
  have hplane : Convex ℝ {z : ℂ | z.im = 0} := by
    intro x hx y hy a b _ _ _
    change (a • x + b • y).im = 0
    simp only [Complex.real_smul, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      (show x.im = 0 from hx), (show y.im = 0 from hy), mul_zero]
  have hsub : centers (twoSteps A D) ⊆ {z : ℂ | z.im = 0} := by
    intro z hz
    simp only [centers, twoSteps, List.map_cons, List.map_nil, Set.mem_setOf_eq,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> simp
  exact convexHull_min hsub hplane hw

theorem twoSteps_lower_bound {A D : ℝ} (hA : 0 < A) (hpi : A ≤ Real.pi)
    (hD : 0 ≤ D) {w : ℂ} (hw : w ∈ convexHull ℝ (centers (twoSteps A D))) :
    (D / 2) * Real.tan (A / 4) ≤ ‖center (twoSteps A D) - w‖ := by
  have ht : 0 ≤ Real.tan (A / 4) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith)
      (by linarith [Real.pi_pos])
  have hb : 0 ≤ (D / 2) * Real.tan (A / 4) := mul_nonneg (by linarith) ht
  have h := Complex.abs_im_le_norm (center (twoSteps A D) - w)
  rw [Complex.sub_im, twoSteps_hull_im_zero A D hw, sub_zero,
    center_twoSteps_im hA hpi, abs_neg, abs_of_nonneg hb] at h
  exact h

/-- For every permitted total angle and every nonnegative endpoint distance,
two equal rotations attain the upper bound. The endpoint distance is exactly D. -/
theorem sharpness {A D : ℝ} (hA : 0 < A) (hpi : A ≤ Real.pi) (hD : 0 ≤ D) :
    totalAngle (twoSteps A D) = A ∧
    (∀ s ∈ twoSteps A D, 0 ≤ s.1) ∧
    (∀ s ∈ twoSteps A D, ∀ t ∈ twoSteps A D, ‖s.2 - t.2‖ ≤ D) ∧
    ‖(D : ℂ) - 0‖ = D ∧
    ∃ w ∈ convexHull ℝ (centers (twoSteps A D)),
      ‖center (twoSteps A D) - w‖ = (D / 2) * Real.tan (A / 4) ∧
      ∀ v ∈ convexHull ℝ (centers (twoSteps A D)),
        (D / 2) * Real.tan (A / 4) ≤ ‖center (twoSteps A D) - v‖ := by
  refine ⟨twoSteps_total A D, twoSteps_nonneg hA.le, twoSteps_pairwise hD,
    endpoints_distance hD, ?_⟩
  obtain ⟨w, hw, hb⟩ := center_near_hull (twoSteps A D) (twoSteps_nonneg hA.le)
    (by simpa only [twoSteps_total] using hA)
    (by simpa only [twoSteps_total] using hpi) D hD (twoSteps_pairwise hD)
  rw [twoSteps_total] at hb
  exact ⟨w, hw, le_antisymm hb (twoSteps_lower_bound hA hpi hD hw),
    fun v hv => twoSteps_lower_bound hA hpi hD hv⟩

#print axioms center_twoSteps_im
#print axioms twoSteps_lower_bound
#print axioms sharpness
end
end RotationSharpness
