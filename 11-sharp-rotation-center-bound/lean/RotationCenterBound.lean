import RotationCoefficients
import ComplexWeightGeometry

/-!
A diameter estimate for the unique center of a literal finite composition of
planar rotations. Nonnegative individual angles and 0 < total angle <= pi are
all the angle hypotheses. No trigonometric estimate is assumed by the result.
-/
namespace RotationCenterBound
noncomputable section
open RotationComposition RotationCoefficients
open scoped BigOperators

theorem sum_map_eq_sum_get {α β : Type*} [AddCommMonoid β]
    (l : List α) (f : α → β) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  rw [← List.sum_ofFn]
  congr 1
  exact (List.ofFn_getElem_eq_map l f).symm

theorem list_weighted_near_convex (l : List (ℂ × ℂ)) (C : Set ℂ) (D : ℝ)
    (hC : Convex ℝ C) (hz : ∀ t ∈ l, t.2 ∈ C)
    (hdiam : ∀ u ∈ C, ∀ v ∈ C, ‖u - v‖ ≤ D)
    (hp : ∀ t ∈ l, 0 ≤ t.1.re)
    (hpsum : (l.map (fun t => t.1.re)).sum = 1)
    (hqsum : (l.map (fun t => t.1.im)).sum = 0) :
    ∃ w ∈ C, ‖(l.map (fun t => t.1 * t.2)).sum - w‖ ≤
      (l.map (fun t => max t.1.im 0)).sum * D := by
  have hp' : ∑ i : Fin l.length, (l.get i).1.re = 1 := by
    simpa only [sum_map_eq_sum_get] using hpsum
  have hq' : ∑ i : Fin l.length, (l.get i).1.im = 0 := by
    simpa only [sum_map_eq_sum_get] using hqsum
  obtain ⟨w, hw, hb⟩ := ComplexWeightGeometry.complex_sum_near_convex
    Finset.univ (fun i : Fin l.length => (l.get i).1.re)
    (fun i : Fin l.length => (l.get i).1.im)
    (fun i : Fin l.length => (l.get i).2) C D hC
    (fun i _ => hz (l.get i) (List.get_mem l i)) hdiam
    (fun i _ => hp (l.get i) (List.get_mem l i)) hp' hq'
  refine ⟨w, hw, ?_⟩
  simpa only [Complex.re_add_im, sum_map_eq_sum_get] using hb

def centers (steps : List Step) : Set ℂ := {z | z ∈ steps.map Prod.snd}

theorem center_near_hull (steps : List Step)
    (hω : ∀ s ∈ steps, 0 ≤ s.1)
    (hpos : 0 < totalAngle steps) (hpi : totalAngle steps ≤ Real.pi)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ s ∈ steps, ∀ t ∈ steps, ‖s.2 - t.2‖ ≤ D) :
    ∃ w ∈ convexHull ℝ (centers steps),
      ‖center steps - w‖ ≤ (D / 2) * Real.tan (totalAngle steps / 4) := by
  let A := totalAngle steps
  have hs : Real.sin (A / 2) ≠ 0 := (half_sin_pos hpos hpi).ne'
  have hden : 1 - factor A ≠ 0 := denominator_ne_zero hpos hpi
  have hhalf : A - A / 2 = A / 2 := by ring
  have hp : ((weighted A steps).map (fun t => t.1.re)).sum = 1 := by
    rw [weighted_re_sum]
    change (Real.sin (A - A / 2) + Real.sin (A / 2)) / (2 * Real.sin (A / 2)) = 1
    rw [hhalf, ← two_mul, div_self (mul_ne_zero (by norm_num) hs)]
  have hq : ((weighted A steps).map (fun t => t.1.im)).sum = 0 := by
    rw [weighted_im_sum]
    change (Real.cos (A / 2) - Real.cos (A - A / 2)) / (2 * Real.sin (A / 2)) = 0
    rw [hhalf, sub_self, zero_div]
  have hz : ∀ t ∈ weighted A steps, t.2 ∈ convexHull ℝ (centers steps) := by
    intro t ht
    apply subset_convexHull ℝ (centers steps)
    change t.2 ∈ steps.map Prod.snd
    rw [← weighted_centers A steps]
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  have hCdiam : ∀ u ∈ convexHull ℝ (centers steps),
      ∀ v ∈ convexHull ℝ (centers steps), ‖u - v‖ ≤ D := by
    intro u hu v hv
    obtain ⟨u', hu', v', hv', huv⟩ := convexHull_exists_dist_ge2 hu hv
    obtain ⟨s, hs', rfl⟩ := List.mem_map.mp hu'
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hv'
    have hdist : ‖u - v‖ ≤ ‖s.2 - t.2‖ := by
      simpa only [dist_eq_norm] using huv
    exact hdist.trans (hdiam s hs' t ht')
  obtain ⟨w, hw, hb⟩ := list_weighted_near_convex (weighted A steps)
    (convexHull ℝ (centers steps)) D (convex_convexHull ℝ _) hz hCdiam
    (weighted_re_nonneg hpos hpi steps hω (le_refl A)) hp hq
  have hcenter : ((weighted A steps).map (fun t => t.1 * t.2)).sum = center steps := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using weighted_product_sum A steps hs
  have hmass := weighted_im_mass_bound hpos hpi steps hω (le_refl A)
  rw [potential_at_total hpos, half_angle_ratio hpos hpi] at hmass
  refine ⟨w, hw, ?_⟩
  rw [hcenter] at hb
  calc
    ‖center steps - w‖ ≤ ((weighted A steps).map (fun t => max t.1.im 0)).sum * D := hb
    _ ≤ (Real.tan (A / 4) / 2) * D := mul_le_mul_of_nonneg_right hmass hD
    _ = (D / 2) * Real.tan (totalAngle steps / 4) := by dsimp [A]; ring

/-- The estimate is attached to the actual composite map and its unique fixed point. -/
theorem composite_rotation_center_near_hull (steps : List Step)
    (hω : ∀ s ∈ steps, 0 ≤ s.1)
    (hpos : 0 < totalAngle steps) (hpi : totalAngle steps ≤ Real.pi)
    (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ s ∈ steps, ∀ t ∈ steps, ‖s.2 - t.2‖ ≤ D) :
    ∃ c : ℂ,
      (∀ z, applyRotations steps z = rotation (totalAngle steps) c z) ∧
      (∀ z, applyRotations steps z = z ↔ z = c) ∧
      ∃ w ∈ convexHull ℝ (centers steps),
        ‖c - w‖ ≤ (D / 2) * Real.tan (totalAngle steps / 4) := by
  refine ⟨center steps, ?_, ?_, center_near_hull steps hω hpos hpi D hD hdiam⟩
  · exact applyRotations_as_rotation_of_angle_bounds steps hpos hpi
  · exact composite_fixed_iff steps (denominator_ne_zero hpos hpi)

#print axioms center_near_hull
#print axioms composite_rotation_center_near_hull
end
end RotationCenterBound
