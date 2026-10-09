import WeightThirtyModel
import Mathlib.Tactic.LinearCombination

namespace BooleanANF

/-- Three simplex support equations already force the entire seven-point affine
cube. This avoids an affine-span dimension argument and preserves the labels. -/
theorem seven_point_affine_cube (a b c d e f g : Block)
    (h₁ : a + d + e + g = 0)
    (h₂ : b + d + f + g = 0)
    (h₃ : c + e + f + g = 0) :
    ∃ p : Block,
      d = p + a + b ∧ e = p + a + c ∧ f = p + b + c ∧ g = a + b + c := by
  refine ⟨d+a+b, ?_, ?_, ?_, ?_⟩
  · funext i
    simp only [Pi.add_apply]
    ring_nf
    simp [CharTwo.two_eq_zero]
  all_goals
    funext i
    have h₁ := congrFun h₁ i
    have h₂ := congrFun h₂ i
    have h₃ := congrFun h₃ i
    simp only [Pi.add_apply, Pi.zero_apply] at *
  · linear_combination (norm := skip) h₂ + h₃
    ring_nf
    simp [CharTwo.two_eq_zero]
  · linear_combination (norm := skip) h₁ + h₃
    ring_nf
    simp [CharTwo.two_eq_zero]
  · linear_combination (norm := skip) h₁ + h₂ + h₃
    ring_nf
    simp [CharTwo.two_eq_zero]

abbrev TripleBlock := Fin 3 → F₂

def cubeLinear (p a b c : Block) : TripleBlock →ₗ[F₂] Block :=
  (LinearMap.proj 0).smulRight (a+p) +
  (LinearMap.proj 1).smulRight (b+p) +
  (LinearMap.proj 2).smulRight (c+p)

/-- The seven simplex labels are the restrictions of one affine map. -/
theorem seven_point_affine_parameterization (y : TripleBlock → Block)
    (h₁ : y ![1,0,0] + y ![1,1,0] + y ![1,0,1] + y ![1,1,1] = 0)
    (h₂ : y ![0,1,0] + y ![1,1,0] + y ![0,1,1] + y ![1,1,1] = 0)
    (h₃ : y ![0,0,1] + y ![1,0,1] + y ![0,1,1] + y ![1,1,1] = 0) :
    ∃ (p : Block) (L : TripleBlock →ₗ[F₂] Block), ∀ v, v ≠ 0 → y v = p + L v := by
  obtain ⟨p,hd,he,hf,hg⟩ := seven_point_affine_cube _ _ _ _ _ _ _ h₁ h₂ h₃
  refine ⟨p, cubeLinear p (y ![1,0,0]) (y ![0,1,0]) (y ![0,0,1]), ?_⟩
  have hbits : ∀ a b c : F₂, ![a,b,c] ≠ (0 : TripleBlock) →
      y ![a,b,c] = p + cubeLinear p (y ![1,0,0]) (y ![0,1,0]) (y ![0,0,1]) ![a,b,c] := by
    intro a b c
    fin_cases a <;> fin_cases b <;> fin_cases c <;> intro hv
    · exact False.elim (hv (by ext i; fin_cases i <;> rfl))
    all_goals
      norm_num only [cubeLinear, LinearMap.add_apply, LinearMap.smulRight_apply,
        LinearMap.proj_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, zero_smul, one_smul, zero_add, add_zero] at *
      simp only [hd, he, hf, hg]
      funext i
      simp only [Pi.add_apply]
      ring_nf
      simp [CharTwo.two_eq_zero, CharTwo.add_self_eq_zero, ← add_assoc]
      all_goals try simp only [hd, he, hf, hg, Pi.add_apply]
      all_goals ring_nf
      all_goals simp [CharTwo.two_eq_zero, show (3 : F₂) = 1 from rfl, show (4 : F₂) = 0 from rfl]
  intro v hv
  have heq : v = ![v 0,v 1,v 2] := by funext i; fin_cases i <;> rfl
  rw [heq] at hv ⊢
  exact hbits _ _ _ hv

/-- Injectivity on all nonzero inputs forces injectivity on the missing zero too. -/
theorem linear_injective_of_nonzero_injective {U W : Type*}
    [AddCommGroup U] [Module F₂ U] [AddCommGroup W] [Module F₂ W]
    (L : U →ₗ[F₂] W) (a b : U) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hinj : ∀ x y : U, x ≠ 0 → y ≠ 0 → L x = L y → x = y) :
    Function.Injective L := by
  have hz : ∀ k, L k = 0 → k = 0 := by
    intro k hk
    by_cases h : k = 0
    · exact h
    have he : ∃ v : U, v ≠ 0 ∧ v ≠ -k := by
      by_cases hka : a = -k
      · exact ⟨b,hb,fun hkb => hab (hka.trans hkb.symm)⟩
      · exact ⟨a,ha,hka⟩
    obtain ⟨v,hv,hvk⟩ := he
    have hvk0 : v + k ≠ 0 := by
      intro heq
      exact hvk (eq_neg_of_add_eq_zero_left heq)
    have heq := hinj v (v+k) hv hvk0 (by rw [map_add, hk, add_zero])
    exact (add_left_cancel (show v + k = v + 0 by simpa using heq.symm))
  intro x y hxy
  have hh : L (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hz _ hh)

/-- Distinct simplex rows give an actual affine embedding of a three-flat. -/
theorem seven_point_affine_embedding (y : TripleBlock → Block)
    (h₁ : y ![1,0,0] + y ![1,1,0] + y ![1,0,1] + y ![1,1,1] = 0)
    (h₂ : y ![0,1,0] + y ![1,1,0] + y ![0,1,1] + y ![1,1,1] = 0)
    (h₃ : y ![0,0,1] + y ![1,0,1] + y ![0,1,1] + y ![1,1,1] = 0)
    (hinj : ∀ v w, v ≠ 0 → w ≠ 0 → y v = y w → v = w) :
    ∃ (p : Block) (L : TripleBlock →ₗ[F₂] Block),
      Function.Injective L ∧ ∀ v, v ≠ 0 → y v = p + L v := by
  obtain ⟨p,L,hL⟩ := seven_point_affine_parameterization y h₁ h₂ h₃
  refine ⟨p,L,?_,hL⟩
  apply linear_injective_of_nonzero_injective L ![1,0,0] ![0,1,0]
  · intro h
    have hh := congrFun h 0
    exact (zero_ne_one : (0 : F₂) ≠ 1) (by simpa using hh.symm)
  · intro h
    have hh := congrFun h 1
    exact (zero_ne_one : (0 : F₂) ≠ 1) (by simpa using hh.symm)
  · intro h
    have hh := congrFun h 0
    exact (zero_ne_one : (0 : F₂) ≠ 1) (by simpa using hh.symm)
  · intro v w hv hw heq
    apply hinj v w hv hw
    rw [hL v hv, hL w hw, heq]

open scoped BigOperators

private theorem simplex_filter_zero :
    Finset.univ.filter (fun v : TripleBlock => v 0 = 1) =
    {![1,0,0], ![1,1,0], ![1,0,1], ![1,1,1]} := by decide
private theorem simplex_filter_one :
    Finset.univ.filter (fun v : TripleBlock => v 1 = 1) =
    {![0,1,0], ![1,1,0], ![0,1,1], ![1,1,1]} := by decide
private theorem simplex_filter_two :
    Finset.univ.filter (fun v : TripleBlock => v 2 = 1) =
    {![0,0,1], ![1,0,1], ![0,1,1], ![1,1,1]} := by decide

/-- Coordinate-free input format for the three support first moments. -/
theorem seven_point_embedding_of_moments (y : TripleBlock → Block)
    (hm : ∀ i : Fin 3, ∑ v ∈ Finset.univ.filter (fun v : TripleBlock => v i = 1), y v = 0)
    (hinj : ∀ v w, v ≠ 0 → w ≠ 0 → y v = y w → v = w) :
    ∃ (p : Block) (L : TripleBlock →ₗ[F₂] Block),
      Function.Injective L ∧ ∀ v, v ≠ 0 → y v = p + L v := by
  have h₀ := hm 0
  have h₁ := hm 1
  have h₂ := hm 2
  rw [simplex_filter_zero] at h₀
  rw [simplex_filter_one] at h₁
  rw [simplex_filter_two] at h₂
  simp only [Finset.sum_insert (by decide : (![1,0,0] : TripleBlock) ∉ ({![1,1,0],![1,0,1],![1,1,1]} : Finset TripleBlock)),
    Finset.sum_insert (by decide : (![1,1,0] : TripleBlock) ∉ ({![1,0,1],![1,1,1]} : Finset TripleBlock)),
    Finset.sum_insert (by decide : (![1,0,1] : TripleBlock) ∉ ({![1,1,1]} : Finset TripleBlock)), Finset.sum_singleton] at h₀
  simp only [Finset.sum_insert (by decide : (![0,1,0] : TripleBlock) ∉ ({![1,1,0],![0,1,1],![1,1,1]} : Finset TripleBlock)),
    Finset.sum_insert (by decide : (![1,1,0] : TripleBlock) ∉ ({![0,1,1],![1,1,1]} : Finset TripleBlock)),
    Finset.sum_insert (by decide : (![0,1,1] : TripleBlock) ∉ ({![1,1,1]} : Finset TripleBlock)), Finset.sum_singleton] at h₁
  simp only [Finset.sum_insert (by decide : (![0,0,1] : TripleBlock) ∉ ({![1,0,1],![0,1,1],![1,1,1]} : Finset TripleBlock)),
    Finset.sum_insert (by decide : (![1,0,1] : TripleBlock) ∉ ({![0,1,1],![1,1,1]} : Finset TripleBlock)),
    Finset.sum_insert (by decide : (![0,1,1] : TripleBlock) ∉ ({![1,1,1]} : Finset TripleBlock)), Finset.sum_singleton] at h₂
  exact seven_point_affine_embedding y (by simpa [add_assoc] using h₀)
    (by simpa [add_assoc] using h₁) (by simpa [add_assoc] using h₂) hinj

end BooleanANF
