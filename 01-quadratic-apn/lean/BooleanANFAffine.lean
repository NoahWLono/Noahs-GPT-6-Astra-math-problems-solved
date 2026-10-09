import BooleanANFLinear
import SingletonShear

namespace BooleanANF
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- A canonically affine Boolean function satisfies the actual affine addition identity. -/
theorem HasDegreeLE.affine_add {f : (ι → F₂) → F₂} (hf : HasDegreeLE f 1)
    (x y : ι → F₂) : f (x+y) + f 0 = f x + f y := by
  rw [← reconstruction_all f (x+y), ← reconstruction_all f 0,
    ← reconstruction_all f x, ← reconstruction_all f y,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hc : 1 < s.card
  · simp [hf s hc]
  have hc' : s.card = 0 ∨ s.card = 1 := by omega
  rcases hc' with hc' | hc'
  · have he : s = ∅ := Finset.card_eq_zero.mp hc'
    simp [he, monomial_empty]
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc'
    simp only [monomial_singleton, Pi.add_apply, Pi.zero_apply, mul_zero, add_zero]
    ring

/-- The linear part of a degree-one Boolean function, in mathlib's actual LinearMap type. -/
def affineLinearPart (f : (ι → F₂) → F₂) (hf : HasDegreeLE f 1) :
    (ι → F₂) →ₗ[F₂] F₂ where
  toFun x := f x + f 0
  map_add' x y := by
    rw [hf.affine_add]
    have h0 := CharTwo.add_self_eq_zero (f 0)
    calc
      f x + f y = f x + f y + (f 0 + f 0) := by rw [h0, add_zero]
      _ = (f x + f 0) + (f y + f 0) := by ring
  map_smul' a x := by
    have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    rcases ha with rfl | rfl <;> simp [CharTwo.add_self_eq_zero]

@[simp] theorem affineLinearPart_apply (f : (ι → F₂) → F₂) (hf : HasDegreeLE f 1)
    (x : ι → F₂) : affineLinearPart f hf x = f x + f 0 := rfl

/-- Coordinatewise canonical degree at most one means an actual affine map. -/
theorem exists_linear_part {κ : Type*} [DecidableEq κ] [Fintype κ]
    (a : (ι → F₂) → (κ → F₂))
    (ha : ∀ i, HasDegreeLE (fun x => a x i) 1) :
    ∃ L : (ι → F₂) →ₗ[F₂] (κ → F₂), ∀ x, a x = a 0 + L x := by
  let L : (ι → F₂) →ₗ[F₂] (κ → F₂) :=
    LinearMap.pi (fun i => affineLinearPart (fun x => a x i) (ha i))
  refine ⟨L, ?_⟩
  intro x
  funext i
  change a x i = a 0 i + (a x i + a 0 i)
  have h0 := CharTwo.add_self_eq_zero (a 0 i)
  rw [add_left_comm, h0, add_zero]

/-- The normalization shear is affine in the ordinary linear-algebraic sense. -/
theorem shearMap_affine {f : DoubleBlock → F₂} (hf : HasDegreeLE f 4) :
    ∃ L : DoubleBlock →ₗ[F₂] DoubleBlock,
      ∀ z, shearMap f z = shearMap f 0 + L z := by
  apply exists_linear_part
  intro i
  cases i with
  | inl i =>
    change HasDegreeLE (fun z : DoubleBlock =>
      z (.inl i) + normalizingShift f (fun j => z (.inr j)) i) 1
    have hh : HasDegreeLE
        (fun z : DoubleBlock => normalizingShift f (fun j => z (.inr j)) i) 1 :=
      HasDegreeLE.comp_affine (κ := Fin 4 ⊕ Fin 4)
        (normalizingShift_affine hf i) (fun z j => z (.inr j))
        (fun j => degree_coordinate (ι := Fin 4 ⊕ Fin 4) (.inr j))
    exact (degree_coordinate (ι := Fin 4 ⊕ Fin 4) (.inl i)).add hh
  | inr i =>
    change HasDegreeLE (fun z : DoubleBlock => z (.inr i)) 1
    exact degree_coordinate (ι := Fin 4 ⊕ Fin 4) (.inr i)


/-- A bundled affine equivalence for transporting the eventual affine-flat classification. -/
theorem shearMap_affine_coordinates {f : DoubleBlock → F₂} (hf : HasDegreeLE f 4) :
    ∃ e : DoubleBlock ≃ₗ[F₂] DoubleBlock,
      ∀ z, shearMap f z = shearMap f 0 + e z := by
  obtain ⟨L, hL⟩ := shearMap_affine hf
  have hinj : Function.Injective L := by
    intro x y hxy
    apply Function.Involutive.injective (shearMap_involutive f)
    rw [hL x, hL y, hxy]
  have hsurj : Function.Surjective L := by
    intro y
    refine ⟨shearMap f (shearMap f 0 + y), ?_⟩
    apply add_left_cancel (a := shearMap f 0)
    rw [← hL, shearMap_involutive]
  let eL : DoubleBlock ≃ₗ[F₂] DoubleBlock := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  exact ⟨eL, hL⟩

end BooleanANF
