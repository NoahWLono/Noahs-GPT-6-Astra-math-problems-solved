import BooleanANFTranslation

/-! Simultaneous singleton-fiber shear normalization for quartics on four plus four variables. -/
namespace BooleanANF
open scoped BigOperators
abbrev Block := Fin 4 → F₂
abbrev DoubleBlock := (Fin 4 ⊕ Fin 4) → F₂

def fiber (f : DoubleBlock → F₂) (y : Block) (x : Block) : F₂ := f (Sum.elim x y)

def normalizingShift (f : DoubleBlock → F₂) (y : Block) (i : Fin 4) : F₂ :=
  1 + fiberCoefficient f (Finset.univ.erase i) y

def shearMap (f : DoubleBlock → F₂) (z : DoubleBlock) : DoubleBlock :=
  Sum.elim (fun i => z (.inl i) + normalizingShift f (fun j => z (.inr j)) i)
    (fun j => z (.inr j))

def normalized (f : DoubleBlock → F₂) : DoubleBlock → F₂ := fun z => f (shearMap f z)

/-- The shear is genuinely invertible, with itself as inverse. -/
theorem shearMap_involutive (f : DoubleBlock → F₂) (z : DoubleBlock) :
    shearMap f (shearMap f z) = z := by
  funext i
  cases i with
  | inl i => simp [shearMap, add_assoc, CharTwo.add_self_eq_zero]
  | inr i => rfl

theorem normalizingShift_affine {f : DoubleBlock → F₂} (hf : HasDegreeLE f 4)
    (i : Fin 4) : HasDegreeLE (fun y => normalizingShift f y i) 1 := by
  exact ((degree_const 1).mono (by decide)).add (cubic_fiber_affine hf i)

set_option maxHeartbeats 1200000 in
theorem normalized_degree {f : DoubleBlock → F₂} (hf : HasDegreeLE f 4) :
    HasDegreeLE (normalized f) 4 := by
  apply HasDegreeLE.comp_affine hf (shearMap f)
  intro i
  cases i with
  | inl i =>
    change HasDegreeLE (fun z : DoubleBlock =>
      z (.inl i) + normalizingShift f (fun j => z (.inr j)) i) 1
    have hh : HasDegreeLE
        (fun z : DoubleBlock => normalizingShift f (fun j => z (.inr j)) i) 1 := by
      exact HasDegreeLE.comp_affine (κ := Fin 4 ⊕ Fin 4)
        (normalizingShift_affine hf i) (fun z j => z (.inr j))
        (fun j => degree_coordinate (ι := Fin 4 ⊕ Fin 4) (.inr j))
    exact (degree_coordinate (ι := Fin 4 ⊕ Fin 4) (.inl i)).add hh
  | inr i =>
    change HasDegreeLE (fun z : DoubleBlock => z (.inr i)) 1
    exact degree_coordinate (ι := Fin 4 ⊕ Fin 4) (.inr i)

theorem fiber_normalized (f : DoubleBlock → F₂) (y : Block) :
    fiber (normalized f) y = fun x => fiber f y (x + normalizingShift f y) := by
  rfl

theorem normalized_top (f : DoubleBlock → F₂) (y : Block) :
    fiberCoefficient (normalized f) Finset.univ y = fiberCoefficient f Finset.univ y := by
  exact coefficient_translate_top (fiber f y) (normalizingShift f y)

/-- Every cubic coefficient becomes one whenever the top coefficient is one. -/
theorem normalized_cubic (f : DoubleBlock → F₂) (y : Block)
    (htop : fiberCoefficient f Finset.univ y = 1) (i : Fin 4) :
    fiberCoefficient (normalized f) (Finset.univ.erase i) y = 1 := by
  change coefficient (fun x => fiber f y (x + normalizingShift f y))
    (Finset.univ.erase i) = 1
  rw [coefficient_translate_cubic]
  change fiberCoefficient f (Finset.univ.erase i) y +
    normalizingShift f y i * fiberCoefficient f Finset.univ y = 1
  rw [htop, mul_one]
  simp [normalizingShift, ← add_assoc, add_comm, CharTwo.add_self_eq_zero]

/-- All singleton fibers move to the same point simultaneously. -/
theorem normalized_singleton (f : DoubleBlock → F₂) (y a : Block)
    (h : fiber f y = delta a) : fiber (normalized f) y = delta 0 := by
  have ha : normalizingShift f y = a := by
    funext i
    change 1 + coefficient (fiber f y) (Finset.univ.erase i) = a i
    rw [h, coefficient_delta_cubic]
    simp [← add_assoc, CharTwo.add_self_eq_zero]
  rw [fiber_normalized, h, ha, delta_translate]
  have haa : a + a = 0 := by funext i; exact CharTwo.add_self_eq_zero (a i)
  rw [haa]

/-- A singleton fiber fixes the top coefficient in every other fiber. -/
theorem top_one_of_singleton {f : DoubleBlock → F₂} (hf : HasDegreeLE f 4)
    (y₀ a : Block) (h : fiber f y₀ = delta a) (y : Block) :
    fiberCoefficient f Finset.univ y = 1 := by
  have ht : fiberCoefficient f Finset.univ y₀ = 1 := by
    change coefficient (fiber f y₀) Finset.univ = 1
    rw [h, coefficient_delta_top]
  rw [top_fiber_constant hf y, ← top_fiber_constant hf y₀, ht]

/-- A four-variable set of size greater than two is top or near-top. -/
private theorem large_four_subset (s : Finset (Fin 4)) (hs : 2 < s.card) :
    s = Finset.univ ∨ ∃ i, s = Finset.univ.erase i := by
  revert s
  decide

/-- After normalization the difference from delta-zero is quadratic in each x-fiber. -/
theorem normalized_residual_quadratic (f : DoubleBlock → F₂) (y : Block)
    (htop : fiberCoefficient f Finset.univ y = 1) :
    HasDegreeLE (fun x => fiber (normalized f) y x + delta 0 x) 2 := by
  intro s hs
  rw [coefficient_add]
  rcases large_four_subset s hs with rfl | ⟨i, rfl⟩
  · change fiberCoefficient (normalized f) Finset.univ y + coefficient (delta 0) Finset.univ = 0
    rw [normalized_top, htop, coefficient_delta_top]
    exact CharTwo.add_self_eq_zero 1
  · change fiberCoefficient (normalized f) (Finset.univ.erase i) y +
      coefficient (delta 0) (Finset.univ.erase i) = 0
    rw [normalized_cubic f y htop i, coefficient_delta_cubic]
    simp [CharTwo.add_self_eq_zero]

end BooleanANF
