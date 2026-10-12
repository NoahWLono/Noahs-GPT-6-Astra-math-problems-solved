import RotationComposition
import Mathlib.Algebra.BigOperators.Fin

namespace RotationCoefficients
noncomputable section
open RotationComposition
open scoped BigOperators

def coeff (A r w : ℝ) : ℂ :=
  ⟨(Real.sin (r + w - A / 2) - Real.sin (r - A / 2)) /
      (2 * Real.sin (A / 2)),
   (Real.cos (r - A / 2) - Real.cos (r + w - A / 2)) /
      (2 * Real.sin (A / 2))⟩

def potential (A t : ℝ) : ℝ :=
  (1 - Real.cos (max (t - A / 2) 0)) / (2 * Real.sin (A / 2))

theorem half_sin_pos {A : ℝ} (hA : 0 < A) (hApi : A ≤ Real.pi) :
    0 < Real.sin (A / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]

theorem factor_euler (t : ℝ) :
    factor t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I :=
  Complex.exp_ofReal_mul_I t

theorem coefficient_identity (A r w : ℝ) (hs : Real.sin (A / 2) ≠ 0) :
    (1 - factor A) * coeff A r w = factor r * (1 - factor w) := by
  have hden : 1 - factor A =
      factor (A / 2) * (-2 * (Real.sin (A / 2) : ℂ) * Complex.I) := by
    have hh : factor (A / 2) * factor (-(A / 2)) = 1 := by
      rw [← factor_add]
      convert factor_zero using 1 <;> ring
    calc
      1 - factor A = factor (A / 2) *
          (factor (-(A / 2)) - factor (A / 2)) := by
        rw [mul_sub, hh, ← factor_add]
        congr 2 <;> ring
      _ = _ := by
        rw [factor_euler (-(A / 2)), factor_euler (A / 2)]
        simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
        ring
  have hcore : (-2 * (Real.sin (A / 2) : ℂ) * Complex.I) * coeff A r w =
      factor (r - A / 2) - factor (r + w - A / 2) := by
    rw [factor_euler, factor_euler]
    apply Complex.ext <;>
      simp only [coeff, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re,
        Complex.sub_im, Complex.add_re, Complex.add_im, Complex.neg_re,
        Complex.neg_im, (show (2 : ℂ).re = 2 from rfl),
        (show (2 : ℂ).im = 0 from rfl)] <;>
      norm_num only at * <;> field_simp [hs] <;> ring
  rw [hden, mul_assoc, hcore, mul_sub, ← factor_add, ← factor_add]
  have hleft : A / 2 + (r - A / 2) = r := by ring
  have hright : A / 2 + (r + w - A / 2) = r + w := by ring
  rw [hleft, hright, factor_add]
  ring

theorem coeff_re_nonneg {A r w : ℝ} (hA : 0 < A) (hApi : A ≤ Real.pi)
    (hr : 0 ≤ r) (hw : 0 ≤ w) (hrw : r + w ≤ A) : 0 ≤ (coeff A r w).re := by
  apply div_nonneg _ (le_of_lt (mul_pos (by norm_num) (half_sin_pos hA hApi)))
  apply sub_nonneg.mpr
  apply Real.sin_le_sin_of_le_of_le_pi_div_two <;> linarith

/-- The positive drops of cosine are dominated by drops after clipping at zero. -/
theorem cosine_positive_drop {x y : ℝ} (hx : -Real.pi ≤ x)
    (hy : y ≤ Real.pi) (hxy : x ≤ y) :
    max (Real.cos x - Real.cos y) 0 ≤
      Real.cos (max x 0) - Real.cos (max y 0) := by
  by_cases hx0 : 0 ≤ x
  · have hy0 : 0 ≤ y := hx0.trans hxy
    have hc : Real.cos y ≤ Real.cos x :=
      Real.cos_le_cos_of_nonneg_of_le_pi hx0 hy hxy
    rw [max_eq_left hx0, max_eq_left hy0, max_eq_left (sub_nonneg.mpr hc)]
  · have hxle : x ≤ 0 := le_of_not_ge hx0
    by_cases hy0 : 0 ≤ y
    · rw [max_eq_right hxle, max_eq_left hy0, Real.cos_zero]
      apply max_le
      · linarith [Real.cos_le_one x]
      · linarith [Real.cos_le_one y]
    · have hyle : y ≤ 0 := le_of_not_ge hy0
      have hc : Real.cos x ≤ Real.cos y := by
        have h := Real.cos_le_cos_of_nonneg_of_le_pi
          (show 0 ≤ -y by linarith) (show -x ≤ Real.pi by linarith)
          (show -y ≤ -x by linarith)
        simpa only [Real.cos_neg] using h
      rw [max_eq_right hxle, max_eq_right hyle, sub_self,
        max_eq_right (sub_nonpos.mpr hc)]

theorem coeff_im_positive_bound {A r w : ℝ} (hA : 0 < A)
    (hApi : A ≤ Real.pi) (hr : 0 ≤ r) (hw : 0 ≤ w) (hrw : r + w ≤ A) :
    max (coeff A r w).im 0 ≤ potential A (r + w) - potential A r := by
  have hd : 0 < 2 * Real.sin (A / 2) :=
    mul_pos (by norm_num) (half_sin_pos hA hApi)
  have hc := cosine_positive_drop
    (show -Real.pi ≤ r - A / 2 by linarith [Real.pi_pos])
    (show r + w - A / 2 ≤ Real.pi by linarith [Real.pi_pos])
    (show r - A / 2 ≤ r + w - A / 2 by linarith)
  change max ((Real.cos (r - A / 2) - Real.cos (r + w - A / 2)) /
    (2 * Real.sin (A / 2))) 0 ≤ _
  rw [← zero_div (2 * Real.sin (A / 2)), max_div_div_right hd.le]
  unfold potential
  rw [← sub_div]
  apply (div_le_div_iff_of_pos_right hd).2
  linarith

theorem potential_at_total {A : ℝ} (hA : 0 < A) :
    potential A A = (1 - Real.cos (A / 2)) / (2 * Real.sin (A / 2)) := by
  have h : A - A / 2 = A / 2 := by ring
  simp only [potential, h, max_eq_left (show 0 ≤ A / 2 by linarith)]

theorem half_angle_ratio {A : ℝ} (hA : 0 < A) (hApi : A ≤ Real.pi) :
    (1 - Real.cos (A / 2)) / (2 * Real.sin (A / 2)) =
      Real.tan (A / 4) / 2 := by
  have hs : Real.sin (A / 4) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have hc : Real.cos (A / 4) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).ne'
  have hh : A / 2 = 2 * (A / 4) := by ring
  rw [hh, Real.cos_two_mul_eq_one_sub, Real.sin_two_mul, Real.tan_eq_sin_div_cos]
  field_simp [hs, hc]
  ring


def weighted (A : ℝ) : List Step → List (ℂ × ℂ)
  | [] => []
  | s :: rest => (coeff A (totalAngle rest) s.1, s.2) :: weighted A rest

theorem totalAngle_nonneg (steps : List Step) (h : ∀ s ∈ steps, 0 ≤ s.1) :
    0 ≤ totalAngle steps := by
  induction steps with
  | nil => exact le_refl 0
  | cons s rest ih =>
      exact add_nonneg (h s (by simp))
        (ih (fun t ht => h t (by simp [ht])))

theorem weighted_centers (A : ℝ) (steps : List Step) :
    (weighted A steps).map Prod.snd = steps.map Prod.snd := by
  induction steps with
  | nil => rfl
  | cons s rest ih => simp [weighted, ih]

theorem weighted_re_sum (A : ℝ) (steps : List Step) :
    ((weighted A steps).map (fun t => t.1.re)).sum =
      (Real.sin (totalAngle steps - A / 2) + Real.sin (A / 2)) /
        (2 * Real.sin (A / 2)) := by
  induction steps with
  | nil => simp [weighted, totalAngle]
  | cons s rest ih =>
      simp only [weighted, List.map_cons, List.sum_cons, ih, coeff, totalAngle]
      rw [add_comm s.1 (totalAngle rest)]
      ring

theorem weighted_im_sum (A : ℝ) (steps : List Step) :
    ((weighted A steps).map (fun t => t.1.im)).sum =
      (Real.cos (A / 2) - Real.cos (totalAngle steps - A / 2)) /
        (2 * Real.sin (A / 2)) := by
  induction steps with
  | nil => simp [weighted, totalAngle]
  | cons s rest ih =>
      simp only [weighted, List.map_cons, List.sum_cons, ih, coeff, totalAngle]
      rw [add_comm s.1 (totalAngle rest)]
      ring

theorem weighted_product_sum (A : ℝ) (steps : List Step)
    (hs : Real.sin (A / 2) ≠ 0) :
    (1 - factor A) * ((weighted A steps).map (fun t => t.1 * t.2)).sum =
      numerator steps := by
  induction steps with
  | nil => simp [weighted, numerator]
  | cons s rest ih =>
      simp only [weighted, List.map_cons, List.sum_cons, numerator]
      rw [mul_add, ← mul_assoc, coefficient_identity A (totalAngle rest) s.1 hs, ih]

theorem weighted_re_nonneg {A : ℝ} (hA : 0 < A) (hApi : A ≤ Real.pi)
    (steps : List Step) (hω : ∀ s ∈ steps, 0 ≤ s.1) (hbound : totalAngle steps ≤ A) :
    ∀ t ∈ weighted A steps, 0 ≤ t.1.re := by
  induction steps with
  | nil => simp [weighted]
  | cons s rest ih =>
      have hs : 0 ≤ s.1 := hω s (by simp)
      have hr : ∀ t ∈ rest, 0 ≤ t.1 := fun t ht => hω t (by simp [ht])
      have hr0 := totalAngle_nonneg rest hr
      have hrA : totalAngle rest ≤ A := by
        change s.1 + totalAngle rest ≤ A at hbound
        linarith
      intro t ht
      rcases List.mem_cons.mp ht with ht | ht
      · subst t
        apply coeff_re_nonneg hA hApi hr0 hs
        simpa only [totalAngle, add_comm] using hbound
      · exact ih hr hrA t ht

theorem weighted_im_mass_bound {A : ℝ} (hA : 0 < A) (hApi : A ≤ Real.pi)
    (steps : List Step) (hω : ∀ s ∈ steps, 0 ≤ s.1) (hbound : totalAngle steps ≤ A) :
    ((weighted A steps).map (fun t => max t.1.im 0)).sum ≤
      potential A (totalAngle steps) := by
  induction steps with
  | nil =>
      simp [weighted, totalAngle, potential,
        max_eq_right (show -(A / 2) ≤ 0 by linarith)]
  | cons s rest ih =>
      have hs : 0 ≤ s.1 := hω s (by simp)
      have hr : ∀ t ∈ rest, 0 ≤ t.1 := fun t ht => hω t (by simp [ht])
      have hr0 := totalAngle_nonneg rest hr
      have hrA : totalAngle rest ≤ A := by
        change s.1 + totalAngle rest ≤ A at hbound
        linarith
      have hstep := coeff_im_positive_bound hA hApi hr0 hs
        (show totalAngle rest + s.1 ≤ A by
          simpa only [totalAngle, add_comm] using hbound)
      have htail := ih hr hrA
      simp only [weighted, List.map_cons, List.sum_cons, totalAngle]
      rw [add_comm s.1 (totalAngle rest)]
      linarith

#print axioms coefficient_identity
#print axioms coeff_im_positive_bound
#print axioms half_angle_ratio
#print axioms weighted_product_sum
#print axioms weighted_re_nonneg
#print axioms weighted_im_mass_bound
end
end RotationCoefficients
