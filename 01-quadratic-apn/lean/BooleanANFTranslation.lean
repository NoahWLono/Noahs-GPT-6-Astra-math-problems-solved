import BooleanANFFibers

namespace BooleanANF
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem delta_expansion (f : (ι → F₂) → F₂) (x : ι → F₂) :
    (∑ p : ι → F₂, f p * delta p x) = f x := by
  simp [delta, mul_ite]

theorem delta_translate (p a : ι → F₂) :
    (fun x => delta p (x + a)) = delta (p + a) := by
  funext x
  have haa : a + a = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have he : x + a = p ↔ x = p + a := by
    constructor
    · intro h
      rw [← h, add_assoc, haa, add_zero]
    · intro h
      rw [h, add_assoc, haa, add_zero]
  simp only [delta, he]

/-- The top coefficient is the sum of the truth table. -/
theorem coefficient_top_eq_sum (f : (ι → F₂) → F₂) :
    coefficient f Finset.univ = ∑ x, f x := by
  have he : f = fun x => ∑ p : ι → F₂, f p * delta p x :=
    funext (fun x => (delta_expansion f x).symm)
  rw [he, coefficient_sum]
  simp only [coefficient_smul, coefficient_delta_top, mul_one]
  simp only [delta_expansion]

/-- A near-top coefficient is the truth-table sum weighted by the missing coordinate. -/
theorem coefficient_cubic_eq_sum (f : (ι → F₂) → F₂) (i : ι) :
    coefficient f (Finset.univ.erase i) = ∑ x, f x * (1 + x i) := by
  have he : f = fun x => ∑ p : ι → F₂, f p * delta p x :=
    funext (fun x => (delta_expansion f x).symm)
  rw [he, coefficient_sum]
  simp only [coefficient_smul, coefficient_delta_cubic, delta_expansion]

/-- Translation preserves the top coefficient. -/
theorem coefficient_translate_top (f : (ι → F₂) → F₂) (a : ι → F₂) :
    coefficient (fun x => f (x + a)) Finset.univ = coefficient f Finset.univ := by
  have he : (fun x => f (x + a)) =
      fun x => ∑ p : ι → F₂, f p * delta (p + a) x := by
    funext x
    rw [← delta_expansion f (x + a)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← delta_translate]
  rw [he, coefficient_sum, coefficient_top_eq_sum]
  simp only [coefficient_smul, coefficient_delta_top, mul_one]

/-- Translation adds a times the top coefficient to each near-top coefficient. -/
theorem coefficient_translate_cubic (f : (ι → F₂) → F₂) (a : ι → F₂) (i : ι) :
    coefficient (fun x => f (x + a)) (Finset.univ.erase i) =
      coefficient f (Finset.univ.erase i) + a i * coefficient f Finset.univ := by
  have he : (fun x => f (x + a)) =
      fun x => ∑ p : ι → F₂, f p * delta (p + a) x := by
    funext x
    rw [← delta_expansion f (x + a)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← delta_translate]
  rw [he, coefficient_sum, coefficient_cubic_eq_sum, coefficient_top_eq_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [coefficient_smul, coefficient_delta_cubic]
  simp only [Pi.add_apply]
  ring


/-- Summing out a block of variables lowers the total degree by its dimension. -/
theorem HasDegreeLE.sum_fibers {κ : Type*} [DecidableEq κ] [Fintype κ]
    {f : ((ι ⊕ κ) → F₂) → F₂} {d : ℕ}
    (hf : HasDegreeLE f (d + Fintype.card κ)) :
    HasDegreeLE (fun x => ∑ y : κ → F₂, f (Sum.elim x y)) d := by
  intro s hs
  rw [coefficient_sum]
  change (∑ y : κ → F₂, BooleanANF.fiberCoefficient f s y) = 0
  rw [← coefficient_top_eq_sum, coefficient_fiberCoefficient]
  apply hf
  simpa using Nat.add_lt_add_right hs (Fintype.card κ)

end BooleanANF
