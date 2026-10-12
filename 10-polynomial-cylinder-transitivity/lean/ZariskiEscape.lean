module
public import ZariskiFibres

@[expose] public section

noncomputable section
namespace ZariskiCylinder
open Polynomial
variable {k : Type*} [Field k] [CharZero k]

/-- Every desired divided-difference value occurs when the polynomial is surjective. -/
theorem difference_surjective (P : k[X]) (hP : Function.Surjective P.eval)
    (t q : k) (hq : q ≠ 0) : Function.Surjective (difference P t q) := by
  intro h
  obtain ⟨v, hv⟩ := hP (P.eval t + q * h)
  change P.eval v = P.eval t + q * h at hv
  refine ⟨(v - t) / q, ?_⟩
  apply mul_left_cancel₀ hq
  rw [← difference_mul]
  have ht : t + q * ((v - t) / q) = v := by field_simp; ring
  rw [ht, hv]
  ring

/-- The two test values 1 and 2 cannot both leave the x coordinate zero. -/
theorem escape_value (p : Point k) (ha : av p ≠ 0) (hc : cv p ≠ 0) :
    ∃ h : k, 2 * mv p * h - 4 * av p * p.y ^ 2 * h ^ 2 ≠ 0 := by
  by_cases h₁ : 2 * mv p - 4 * av p * p.y ^ 2 = 0
  · refine ⟨2, ?_⟩
    intro h₂
    have hyy : av p * p.y ^ 2 = 0 := by linear_combination h₁ / 4 - h₂ / 8
    have hy : p.y = 0 := by
      have hsq : p.y ^ 2 = 0 := (mul_eq_zero.mp hyy).resolve_left ha
      simpa using hsq
    have hm : mv p = 0 := by rw [hy] at h₁; linear_combination h₁ / 2
    have hmcv := mv_add_cv p
    rw [hy, hm] at hmcv
    exact hc (by simpa using hmcv)
  · refine ⟨1, ?_⟩
    simpa using h₁

/-- One extra move leaves the zero-x fibre whenever a and c are nonzero. -/
theorem escape_extra (P : k[X]) (hP : Function.Surjective P.eval)
    (p : Point k) (hx : p.x = 0) (ha : av p ≠ 0) (hc : cv p ≠ 0) :
    ∃ q : Point k, Reaches P 1 p q ∧ q.x ≠ 0 := by
  have hq : 2 * av p * cv p ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ha) hc
  obtain ⟨h, hh⟩ := escape_value p ha hc
  obtain ⟨s, hs⟩ := difference_surjective P hP p.t (2 * av p * cv p) hq h
  refine ⟨extra P p s, Reaches.single (.extra p s), ?_⟩
  simpa only [extra, eStep_x, hx, zero_add, hs] using hh

/-- The boundary can be left in at most three of the displayed moves. -/
theorem escape_boundary (P : k[X]) (hP : Function.Surjective P.eval)
    (p : Point k) (hx : p.x = 0) :
    ∃ q : Point k, Reaches P 3 p q ∧ q.x ≠ 0 := by
  by_cases hz : p.z = 0
  · let p₁ := tau p (1 - p.u)
    have h₁x : p₁.x = 0 := hx
    have h₁a : av p₁ = 1 := by simp [p₁, av, tau, hx, hz]
    have h₁c : cv p₁ = -2 := by
      simp only [cv, h₁a]
      simp [p₁, tau, hx, hz]
    obtain ⟨q, hq, hxq⟩ := escape_extra P hP p₁ h₁x (by rw [h₁a]; exact one_ne_zero)
      (by rw [h₁c]; norm_num)
    exact ⟨q, .pad ((Reaches.single (.tau p _)).trans hq), hxq⟩
  · let p₁ := tau p (-p.u)
    let p₂ := deltaZ p₁ ((p₁.y - 1) / (2 * p.z))
    have h₁x : p₁.x = 0 := hx
    have h₁z : p₁.z = p.z := by simp [p₁, tau, hx]
    have h₁u : p₁.u = 0 := by simp [p₁, tau]
    have h₂x : p₂.x = 0 := hx
    have h₂z : p₂.z = p.z := by simp [p₂, deltaZ, h₁x, h₁z]
    have h₂u : p₂.u = 0 := h₁u
    have h₂y : p₂.y = 1 := by
      simp only [p₂, deltaZ, h₁x, h₁z, zero_mul, add_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
      field_simp
      ring
    have h₂a : av p₂ = 1 := by simp [av, h₂x, h₂u]
    have h₂c : cv p₂ = p.z := by simp [cv, h₂z, h₂y, h₂u]
    obtain ⟨q, hq, hxq⟩ := escape_extra P hP p₂ h₂x (by rw [h₂a]; exact one_ne_zero)
      (by rwa [h₂c])
    exact ⟨q, (Reaches.step (Reaches.single (.tau p _)) (.deltaZ p₁ _)).trans hq, hxq⟩

/-- Every point reaches a nonzero-x point in at most three moves. -/
theorem reach_nonzero (P : k[X]) (hP : Function.Surjective P.eval) (p : Point k) :
    ∃ q : Point k, Reaches P 3 p q ∧ q.x ≠ 0 := by
  by_cases hx : p.x = 0
  · exact escape_boundary P hP p hx
  · exact ⟨p, .pad (.pad (.pad (.refl p))), hx⟩

#print axioms escape_boundary
end ZariskiCylinder
