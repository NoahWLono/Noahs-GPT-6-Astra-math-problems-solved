import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The geometric part of the rotation-center estimate. The weights are explicit
hypotheses here; this module does not assert that rotation coefficients satisfy
them. All sums are finite, and no boundedness is hidden in metric diameter.
-/
namespace ComplexWeightGeometry
noncomputable section
open scoped BigOperators

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem positive_mass_eq_negative_mass (s : Finset ι) (q : ι → ℝ)
    (hq : ∑ i ∈ s, q i = 0) :
    ∑ i ∈ s, max (q i) 0 = ∑ i ∈ s, max (-q i) 0 := by
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  simpa only [max_zero_sub_max_neg_zero_eq_self] using hq

theorem signed_sum_norm_le (s : Finset ι) (q : ι → ℝ) (z : ι → E)
    (C : Set E) (D : ℝ) (hC : Convex ℝ C)
    (hz : ∀ i ∈ s, z i ∈ C)
    (hdiam : ∀ u ∈ C, ∀ v ∈ C, ‖u - v‖ ≤ D)
    (hq : ∑ i ∈ s, q i = 0) :
    ‖∑ i ∈ s, q i • z i‖ ≤ (∑ i ∈ s, max (q i) 0) * D := by
  let Q : ℝ := ∑ i ∈ s, max (q i) 0
  have hQnonneg : 0 ≤ Q := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  have hneg : ∑ i ∈ s, max (-q i) 0 = Q :=
    (positive_mass_eq_negative_mass s q hq).symm
  change ‖∑ i ∈ s, q i • z i‖ ≤ Q * D
  by_cases hQzero : Q = 0
  · have hpzero : ∀ i ∈ s, max (q i) 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => le_max_right (q i) 0)).mp hQzero
    have hnzero : ∀ i ∈ s, max (-q i) 0 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => le_max_right (-q i) 0)).mp
        (hneg.trans hQzero)
    have hqzero : ∀ i ∈ s, q i = 0 := by
      intro i hi
      rw [← max_zero_sub_max_neg_zero_eq_self (q i), hpzero i hi, hnzero i hi]
      simp
    simp only [hQzero, zero_mul, norm_le_zero_iff]
    exact Finset.sum_eq_zero (fun i hi => by rw [hqzero i hi, zero_smul])
  · let u : E := ∑ i ∈ s, (Q⁻¹ * max (q i) 0) • z i
    let v : E := ∑ i ∈ s, (Q⁻¹ * max (-q i) 0) • z i
    have hu : u ∈ C := by
      apply hC.sum_mem (fun i _ => mul_nonneg (inv_nonneg.mpr hQnonneg)
        (le_max_right _ _)) _ hz
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hQzero
    have hv : v ∈ C := by
      apply hC.sum_mem (fun i _ => mul_nonneg (inv_nonneg.mpr hQnonneg)
        (le_max_right _ _)) _ hz
      rw [← Finset.mul_sum, hneg, inv_mul_cancel₀ hQzero]
    have hdecomp : ∑ i ∈ s, q i • z i = Q • (u - v) := by
      dsimp [u, v]
      rw [smul_sub, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [smul_smul, ← mul_assoc, mul_inv_cancel₀ hQzero, one_mul,
        ← sub_smul, max_zero_sub_max_neg_zero_eq_self]
    rw [hdecomp, norm_smul, Real.norm_of_nonneg hQnonneg]
    exact mul_le_mul_of_nonneg_left (hdiam u hu v hv) hQnonneg

/-- Complex weights with nonnegative real parts summing to one and zero total
imaginary part lie within positive-imaginary-mass times diameter of a convex set. -/
theorem complex_sum_near_convex (s : Finset ι) (p q : ι → ℝ) (z : ι → ℂ)
    (C : Set ℂ) (D : ℝ) (hC : Convex ℝ C)
    (hz : ∀ i ∈ s, z i ∈ C)
    (hdiam : ∀ u ∈ C, ∀ v ∈ C, ‖u - v‖ ≤ D)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpsum : ∑ i ∈ s, p i = 1)
    (hqsum : ∑ i ∈ s, q i = 0) :
    ∃ w ∈ C,
      ‖(∑ i ∈ s, ((p i : ℂ) + (q i : ℂ) * Complex.I) * z i) - w‖ ≤
        (∑ i ∈ s, max (q i) 0) * D := by
  refine ⟨∑ i ∈ s, p i • z i, hC.sum_mem hp hpsum hz, ?_⟩
  have hsplit :
      (∑ i ∈ s, ((p i : ℂ) + (q i : ℂ) * Complex.I) * z i) -
        (∑ i ∈ s, p i • z i) = Complex.I * (∑ i ∈ s, q i • z i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.real_smul]
    ring
  rw [hsplit, norm_mul, Complex.norm_I, one_mul]
  exact signed_sum_norm_le s q z C D hC hz hdiam hqsum

/-- Pairwise diameter bounds on the original finite centers suffice. -/
theorem complex_sum_near_hull (s : Finset ι) (p q : ι → ℝ) (z : ι → ℂ)
    (D : ℝ) (hdiam : ∀ i ∈ s, ∀ j ∈ s, ‖z i - z j‖ ≤ D)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpsum : ∑ i ∈ s, p i = 1)
    (hqsum : ∑ i ∈ s, q i = 0) :
    ∃ w ∈ convexHull ℝ (z '' (s : Set ι)),
      ‖(∑ i ∈ s, ((p i : ℂ) + (q i : ℂ) * Complex.I) * z i) - w‖ ≤
        (∑ i ∈ s, max (q i) 0) * D := by
  refine complex_sum_near_convex s p q z (convexHull ℝ (z '' (s : Set ι))) D
    (convex_convexHull ℝ _) ?_ ?_ hp hpsum hqsum
  · intro i hi
    exact subset_convexHull ℝ _ ⟨i, hi, rfl⟩
  · intro u hu v hv
    obtain ⟨u', ⟨i, hi, rfl⟩, v', ⟨j, hj, rfl⟩, huv⟩ :=
      convexHull_exists_dist_ge2 hu hv
    have huv' : ‖u - v‖ ≤ ‖z i - z j‖ := by
      simpa only [dist_eq_norm] using huv
    exact huv'.trans (hdiam i hi j hj)

#print axioms signed_sum_norm_le
#print axioms complex_sum_near_convex
#print axioms complex_sum_near_hull

end
end ComplexWeightGeometry
