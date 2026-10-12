import Mathlib.Order.Hom.Set
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Finite order rigidity and a three-point strict-convexity obstruction. -/
set_option autoImplicit false
open Set
namespace PillaiFiniteOrder

/-- Two similarly ordered enumerations of the same finite ordered set coincide. -/
theorem finite_strictMono_eq {α : Type*} [LinearOrder α] [Finite α]
    {f g : α → ℝ} (hf : StrictMono f) (hg : StrictMono g)
    (hr : Set.range f=Set.range g) : f=g := by
  exact (hf.range_inj hg).mp hr

/-- A common value at the largest argument excludes opposing orientations. -/
theorem opposite_orientations_impossible {α : Type*} [LinearOrder α]
    {f g : α → ℝ} (hf : StrictMono f) (hg : StrictAnti g)
    (hr : Set.range f=Set.range g) (b : α) (hb : ∀ x,x≤b)
    (he : f b=g b) (hx : ∃ x,x<b) : False := by
  obtain ⟨x,hx⟩ := hx
  have hm : f x∈Set.range g := hr ▸ Set.mem_range_self x
  obtain ⟨y,hy⟩ := hm
  have h₁ := hf hx
  have h₂ := hg.antitone (hb y)
  linarith

/-- Finite monotone/antitone functions with equal images and a common maximum argument agree. -/
theorem finite_order_rigidity {α : Type*} [LinearOrder α] [Finite α]
    {f g : α → ℝ} (hf : StrictMono f ∨ StrictAnti f) (hg : StrictMono g ∨ StrictAnti g)
    (hr : Set.range f=Set.range g) (b : α) (hb : ∀ x,x≤b)
    (he : f b=g b) (hx : ∃ x,x<b) : f=g := by
  rcases hf with hf | hf <;> rcases hg with hg | hg
  · exact finite_strictMono_eq hf hg hr
  · exact (opposite_orientations_impossible hf hg hr b hb he hx).elim
  · exact (opposite_orientations_impossible hg hf hr.symm b hb he.symm hx).elim
  · exact finite_strictMono_eq (α := αᵒᵈ) (fun _ _ h ↦ hf h) (fun _ _ h ↦ hg h) hr

/-- A natural power of exponent at least two cannot agree with an affine function at three
nonnegative, strictly ordered arguments. The endpoint zero is allowed. -/
theorem power_three_points_impossible (m : ℕ) (hm : 2≤m) (x y z α β : ℝ)
    (hx : 0≤x) (hxy : x<y) (hyz : y<z)
    (he₁ : x^m=α+β*x) (he₂ : y^m=α+β*y) (he₃ : z^m=α+β*z) : False := by
  have hc : StrictConvexOn ℝ (Set.Ici 0) (fun t : ℝ ↦ t^m) := by
    simpa only [Real.rpow_natCast] using
      (strictConvexOn_rpow (p := (m : ℝ)) (by exact_mod_cast (show 1<m by omega)))
  have hz : 0≤z := le_trans hx (le_of_lt (lt_trans hxy hyz))
  have hh := hc.slope_strict_mono_adjacent hx hz hxy hyz
  rw [he₁,he₂,he₃] at hh
  have h₁ : (α+β*y-(α+β*x))/(y-x)=β := by rw [div_eq_iff (sub_ne_zero.mpr hxy.ne')]; ring
  have h₂ : (α+β*z-(α+β*y))/(z-y)=β := by rw [div_eq_iff (sub_ne_zero.mpr hyz.ne')]; ring
  rw [h₁,h₂] at hh
  exact lt_irrefl _ hh

/-- The same obstruction without imposing an order on the three supplied arguments. -/
theorem power_three_distinct_impossible (m : ℕ) (hm : 2≤m) (x y z α β : ℝ)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (he₁ : x^m=α+β*x) (he₂ : y^m=α+β*y) (he₃ : z^m=α+β*z) : False := by
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · rcases lt_or_gt_of_ne hyz with hyz | hyz
    · exact power_three_points_impossible m hm x y z α β hx hxy hyz he₁ he₂ he₃
    · rcases lt_or_gt_of_ne hxz with hxz | hxz
      · exact power_three_points_impossible m hm x z y α β hx hxz hyz he₁ he₃ he₂
      · exact power_three_points_impossible m hm z x y α β hz hxz hxy he₃ he₁ he₂
  · rcases lt_or_gt_of_ne hxz with hxz | hxz
    · exact power_three_points_impossible m hm y x z α β hy hxy hxz he₂ he₁ he₃
    · rcases lt_or_gt_of_ne hyz with hyz | hyz
      · exact power_three_points_impossible m hm y z x α β hy hyz hxz he₂ he₃ he₁
      · exact power_three_points_impossible m hm z y x α β hz hyz hxy he₃ he₂ he₁

/-- The precise finite-image obstruction used for sparse complex conjugates. -/
theorem finite_power_affine_impossible (S : Finset ℝ) (m : ℕ) (hm : 2≤m)
    (U V C D : ℝ) (hV : V≠0) (hD : D≠0)
    (hbase : ∀ x : S, 0≤U+V*(x : ℝ))
    (hrange : Set.range (fun x : S ↦ (U+V*(x : ℝ))^m)=
      Set.range (fun x : S ↦ C+D*(x : ℝ)))
    (b : S) (hb : ∀ x : S,x≤b) (hbeq : (U+V*(b : ℝ))^m=C+D*(b : ℝ))
    (hbelow : ∃ x : S,x<b) (x y z : S) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) : False := by
  have hm₀ : m≠0 := by omega
  have hf : StrictMono (fun x : S ↦ (U+V*(x : ℝ))^m) ∨
      StrictAnti (fun x : S ↦ (U+V*(x : ℝ))^m) := by
    rcases lt_or_gt_of_ne hV with hV | hV
    · right
      intro x y hxy
      apply (pow_lt_pow_iff_left₀ (hbase y) (hbase x) hm₀).mpr
      have hh : (x : ℝ)<y := hxy
      nlinarith
    · left
      intro x y hxy
      apply (pow_lt_pow_iff_left₀ (hbase x) (hbase y) hm₀).mpr
      have hh : (x : ℝ)<y := hxy
      nlinarith
  have hg : StrictMono (fun x : S ↦ C+D*(x : ℝ)) ∨
      StrictAnti (fun x : S ↦ C+D*(x : ℝ)) := by
    rcases lt_or_gt_of_ne hD with hD | hD
    · right; intro x y hxy; have hh : (x : ℝ)<y := hxy; nlinarith
    · left; intro x y hxy; have hh : (x : ℝ)<y := hxy; nlinarith
  have heq := finite_order_rigidity hf hg hrange b hb hbeq hbelow
  have hinj : Function.Injective (fun t : S ↦ U+V*(t : ℝ)) := by
    intro t v h
    apply Subtype.ext
    exact mul_left_cancel₀ hV (add_left_cancel h)
  have hpower (t : S) : (U+V*(t : ℝ))^m=(C-D*U/V)+(D/V)*(U+V*(t : ℝ)) := by
    rw [congrFun heq t]
    field_simp
    ring
  exact power_three_distinct_impossible m hm _ _ _ _ _ (hbase x) (hbase y) (hbase z)
    (fun h ↦ hxy (hinj h)) (fun h ↦ hxz (hinj h)) (fun h ↦ hyz (hinj h))
    (hpower x) (hpower y) (hpower z)

end PillaiFiniteOrder
