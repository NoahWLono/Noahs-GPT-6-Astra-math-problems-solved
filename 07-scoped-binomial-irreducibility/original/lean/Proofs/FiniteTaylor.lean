import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import FiniteFourier
import Mathlib.Tactic.GCongr

/-! A direct, finite third-order Taylor estimate for the concrete real-power function. -/

set_option autoImplicit false
open Set

namespace PillaiTaylor

noncomputable def quad (b v : ℝ) : ℝ := 1 - 2 * b * v + v ^ 2
noncomputable def quadD (b v : ℝ) : ℝ := -2 * b + 2 * v
noncomputable def g (a b v : ℝ) : ℝ := (quad b v) ^ a
noncomputable def g₁ (a b v : ℝ) : ℝ := a * (quad b v) ^ (a - 1) * quadD b v
noncomputable def g₂ (a b v : ℝ) : ℝ :=
  a * (a - 1) * (quad b v) ^ (a - 2) * (quadD b v) ^ 2 +
    2 * a * (quad b v) ^ (a - 1)
noncomputable def g₃ (a b v : ℝ) : ℝ :=
  a * (a - 1) * (a - 2) * (quad b v) ^ (a - 3) * (quadD b v) ^ 3 +
    6 * a * (a - 1) * (quad b v) ^ (a - 2) * quadD b v

lemma quad_bounds (b v : ℝ) (hb : |b| ≤ 1) (hv : v ∈ Icc (0 : ℝ) (1/4)) :
    (1/2 : ℝ) ≤ quad b v ∧ |quadD b v| ≤ 3 := by
  rcases abs_le.mp hb with ⟨hb₀,hb₁⟩
  rcases hv with ⟨hv₀,hv₁⟩
  dsimp [quad, quadD]
  constructor
  · have hprod : b * v ≤ v := by nlinarith
    nlinarith [sq_nonneg (v - 1)]
  · apply abs_le.mpr
    constructor <;> nlinarith

lemma quad_hasDerivAt (b v : ℝ) : HasDerivAt (quad b) (quadD b v) v := by
  convert! ((hasDerivAt_const v (1 : ℝ)).sub ((hasDerivAt_id v).const_mul (2*b))).add
    ((hasDerivAt_id v).pow 2) using 1
  simp [quadD]

lemma quadD_hasDerivAt (b v : ℝ) : HasDerivAt (quadD b) 2 v := by
  convert! ((hasDerivAt_id v).const_mul 2).const_add (-2*b) using 1
  simp

lemma g_hasDerivAt (a b v : ℝ) (hq : quad b v ≠ 0) :
    HasDerivAt (g a b) (g₁ a b v) v := by
  convert! (quad_hasDerivAt b v).rpow_const (p := a) (Or.inl hq) using 1
  dsimp [g₁]
  ring

lemma g₁_hasDerivAt (a b v : ℝ) (hq : quad b v ≠ 0) :
    HasDerivAt (g₁ a b) (g₂ a b v) v := by
  have hd := (((quad_hasDerivAt b v).rpow_const (p := a-1) (Or.inl hq)).const_mul a).mul
    (quadD_hasDerivAt b v)
  have he : a - 1 - 1 = a - 2 := by ring
  simp only [he] at hd
  convert! hd using 1
  dsimp [g₂]
  ring

lemma g₂_hasDerivAt (a b v : ℝ) (hq : quad b v ≠ 0) :
    HasDerivAt (g₂ a b) (g₃ a b v) v := by
  have hd₁ := (((quad_hasDerivAt b v).rpow_const (p := a-2) (Or.inl hq)).const_mul
    (a*(a-1))).mul ((quadD_hasDerivAt b v).pow 2)
  have hd₂ := ((quad_hasDerivAt b v).rpow_const (p := a-1) (Or.inl hq)).const_mul (2*a)
  have he₁ : a - 2 - 1 = a - 3 := by ring
  have he₂ : a - 1 - 1 = a - 2 := by ring
  have hd := hd₁.add hd₂
  simp only [he₁,he₂] at hd
  convert! hd using 1
  dsimp [g₃]
  ring

/-- A cubic remainder proved directly by three applications of Rolle's theorem. -/
theorem taylor_three_hasDerivAt (f f₁ f₂ f₃ : ℝ → ℝ) (u : ℝ) (hu : 0 < u)
    (h₀ : ∀ v ∈ Icc (0 : ℝ) u, HasDerivAt f (f₁ v) v)
    (h₁ : ∀ v ∈ Icc (0 : ℝ) u, HasDerivAt f₁ (f₂ v) v)
    (h₂ : ∀ v ∈ Icc (0 : ℝ) u, HasDerivAt f₂ (f₃ v) v) :
    ∃ v ∈ Ioo (0 : ℝ) u,
      f u - (f 0 + f₁ 0 * u + (f₂ 0 / 2) * u ^ 2) = f₃ v * u ^ 3 / 6 := by
  let K := (f u - (f 0 + f₁ 0 * u + (f₂ 0 / 2) * u ^ 2)) / u ^ 3
  let F := fun v ↦ f v - (f 0 + f₁ 0 * v + (f₂ 0 / 2) * v ^ 2) - K * v ^ 3
  let F₁ := fun v ↦ f₁ v - (f₁ 0 + f₂ 0 * v) - (3*K) * v ^ 2
  let F₂ := fun v ↦ f₂ v - f₂ 0 - (6*K) * v
  let F₃ := fun v ↦ f₃ v - 6*K
  have hD₀ (v : ℝ) (hv : v ∈ Icc (0 : ℝ) u) : HasDerivAt F (F₁ v) v := by
    dsimp only [F,F₁]
    convert! ((h₀ v hv).sub ((((hasDerivAt_id v).const_mul (f₁ 0)).const_add (f 0)).add
      (((hasDerivAt_id v).pow 2).const_mul (f₂ 0/2)))).sub
      (((hasDerivAt_id v).pow 3).const_mul K) using 1
    simp only [id_eq]
    ring
  have hD₁ (v : ℝ) (hv : v ∈ Icc (0 : ℝ) u) : HasDerivAt F₁ (F₂ v) v := by
    dsimp only [F₁,F₂]
    convert! ((h₁ v hv).sub (((hasDerivAt_id v).const_mul (f₂ 0)).const_add (f₁ 0))).sub
      (((hasDerivAt_id v).pow 2).const_mul (3*K)) using 1
    simp only [id_eq]
    ring
  have hD₂ (v : ℝ) (hv : v ∈ Icc (0 : ℝ) u) : HasDerivAt F₂ (F₃ v) v := by
    dsimp only [F₂,F₃]
    convert! ((h₂ v hv).sub_const (f₂ 0)).sub
      ((hasDerivAt_id v).const_mul (6*K)) using 1
    ring
  have hF₀ : F 0 = F u := by
    dsimp [F,K]
    simp only [mul_zero, add_zero]
    rw [div_mul_cancel₀ _ (pow_ne_zero 3 hu.ne')]
    ring
  obtain ⟨v₁,hv₁,hv₁z⟩ := exists_hasDerivAt_eq_zero hu
    (fun v hv ↦ (hD₀ v hv).continuousAt.continuousWithinAt) hF₀
    (fun v hv ↦ hD₀ v ⟨hv.1.le,hv.2.le⟩)
  have hF₁ : F₁ 0 = F₁ v₁ := by simp [F₁,hv₁z]
  obtain ⟨v₂,hv₂,hv₂z⟩ := exists_hasDerivAt_eq_zero hv₁.1
    (fun v hv ↦ (hD₁ v ⟨hv.1,hv.2.trans hv₁.2.le⟩).continuousAt.continuousWithinAt) hF₁
    (fun v hv ↦ hD₁ v ⟨hv.1.le,hv.2.le.trans hv₁.2.le⟩)
  have hF₂ : F₂ 0 = F₂ v₂ := by simp [F₂,hv₂z]
  obtain ⟨v₃,hv₃,hv₃z⟩ := exists_hasDerivAt_eq_zero hv₂.1
    (fun v hv ↦ (hD₂ v ⟨hv.1,(hv.2.trans hv₂.2.le).trans hv₁.2.le⟩).continuousAt.continuousWithinAt) hF₂
    (fun v hv ↦ hD₂ v ⟨hv.1.le,(hv.2.le.trans hv₂.2.le).trans hv₁.2.le⟩)
  refine ⟨v₃,⟨hv₃.1,(hv₃.2.trans hv₂.2).trans hv₁.2⟩,?_⟩
  have hK : f₃ v₃ = 6*K := by dsimp [F₃] at hv₃z; linarith
  rw [hK]
  have he : f u - (f 0 + f₁ 0 * u + (f₂ 0 / 2) * u ^ 2) = K * u ^ 3 := by
    dsimp [K]
    rw [div_mul_cancel₀ _ (pow_ne_zero 3 hu.ne')]
  rw [he]
  ring

lemma rpow_shift_bounds (a H : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1/6) (hH : 1/2 ≤ H) :
    H ^ (a-3) ≤ 8 ∧ H ^ (a-2) ≤ 4 := by
  constructor
  · calc
      H ^ (a-3) ≤ (1/2 : ℝ) ^ (a-3) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hH (by linarith)
      _ ≤ (1/2 : ℝ) ^ (-3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 8 := by norm_num [Real.rpow_neg, Real.rpow_ofNat]
  · calc
      H ^ (a-2) ≤ (1/2 : ℝ) ^ (a-2) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hH (by linarith)
      _ ≤ (1/2 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 4 := by norm_num [Real.rpow_neg, Real.rpow_ofNat]

/-- Uniform bound for the concrete third derivative, not an assumed Taylor remainder. -/
theorem g₃_bound (a b v : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1/6) (hb : |b| ≤ 1)
    (hv : v ∈ Icc (0 : ℝ) (1/4)) : |g₃ a b v| ≤ 504*a := by
  have hq := (quad_bounds b v hb hv).1
  have hd := (quad_bounds b v hb hv).2
  have hp := rpow_shift_bounds a (quad b v) ha ha₁ hq
  have hp₂ : 0 ≤ (quad b v) ^ (a-2) := Real.rpow_nonneg (by linarith) _
  have hp₃ : 0 ≤ (quad b v) ^ (a-3) := Real.rpow_nonneg (by linarith) _
  have ha₂ : |a-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have ha₃ : |a-2| ≤ 2 := abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    |g₃ a b v| ≤
        |a*(a-1)*(a-2)*(quad b v)^(a-3)*(quadD b v)^3| +
          |6*a*(a-1)*(quad b v)^(a-2)*quadD b v| := abs_add_le _ _
    _ = a* |a-1| * |a-2| *((quad b v)^(a-3))* |quadD b v| ^3 +
          6*a* |a-1| *((quad b v)^(a-2))* |quadD b v| := by
      simp only [abs_mul, abs_pow, abs_of_pos ha, abs_of_nonneg hp₂,
        abs_of_nonneg hp₃, abs_of_pos (show (0:ℝ) < 6 by norm_num)]
    _ ≤ a*1*2*8*3^3 + 6*a*1*4*3 := by
      gcongr <;> first | exact hp.1 | exact hp.2
    _ = 504*a := by ring

/-- Uniform quadratic Taylor estimate with the paper's exact constant 84. -/
theorem quadratic_rpow_taylor (a b u : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1/6)
    (hb : |b| ≤ 1) (hu : 0 ≤ u) (hu₁ : u ≤ 1/4) :
    |(1 - 2*b*u + u^2)^a -
      (1 - 2*a*b*u + (a + 2*a*(a-1)*b^2)*u^2)| ≤ 84*a*u^3 := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp
  have hq (v : ℝ) (hv : v ∈ Icc (0 : ℝ) u) : quad b v ≠ 0 := by
    have hh := (quad_bounds b v hb ⟨hv.1,hv.2.trans hu₁⟩).1
    linarith
  obtain ⟨v,hv,he⟩ := taylor_three_hasDerivAt (g a b) (g₁ a b) (g₂ a b) (g₃ a b) u hu
    (fun v hv ↦ g_hasDerivAt a b v (hq v hv))
    (fun v hv ↦ g₁_hasDerivAt a b v (hq v hv))
    (fun v hv ↦ g₂_hasDerivAt a b v (hq v hv))
  have hz₀ : g a b 0 = 1 := by simp [g,quad]
  have hz₁ : g₁ a b 0 = -2*a*b := by simp [g₁,quad,quadD]; ring
  have hz₂ : g₂ a b 0 / 2 = a + 2*a*(a-1)*b^2 := by
    simp [g₂,quad,quadD]
    ring
  rw [hz₀,hz₁,hz₂] at he
  have he' : (1 - 2*b*u + u^2)^a -
      (1 - 2*a*b*u + (a + 2*a*(a-1)*b^2)*u^2) = g₃ a b v * u^3 / 6 := by
    convert! he using 1
    dsimp [g,quad]
    ring
  rw [he',abs_div,abs_mul,abs_of_nonneg (pow_nonneg hu.le 3)]
  norm_num only [abs_of_pos (show (0:ℝ) < 6 by norm_num)]
  have hb₃ := g₃_bound a b v ha ha₁ hb ⟨hv.1.le,hv.2.le.trans hu₁⟩
  calc
    |g₃ a b v| * u^3 / 6 ≤ (504*a) * u^3 / 6 := by gcongr
    _ = 84*a*u^3 := by ring

end PillaiTaylor
