import QuadraticFourPolynomial
import QuadraticFourEnumeration

namespace BooleanANF.QuadraticFour

theorem poly_weights (a b c d e f g h i j k : F₂) :
    weight (poly a b c d e f g h i j k) ∈ ({0,4,6,8,10,12,16} : Finset ℕ) :=
  QuadraticFourRaw.all_weights a b c d e f g h i j k

theorem weight_zero_iff (f : V → F₂) : weight f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hh : ∀ x, (f x).val = 0 := by simpa [weight] using h
    funext x
    apply ZMod.val_injective 2
    simpa using hh x
  · rintro rfl
    simp [weight]

theorem quadratic_weights {f : V → F₂} (hf : HasDegreeLE f 2) :
    weight f ∈ ({0,4,6,8,10,12,16} : Finset ℕ) := by
  rw [← representation hf, eval_eq_poly]
  exact poly_weights _ _ _ _ _ _ _ _ _ _ _

theorem quadratic_min_weight {f : V → F₂} (hf : HasDegreeLE f 2) (hn : f ≠ 0) :
    4 ≤ weight f := by
  have hw := quadratic_weights hf
  have hz : weight f ≠ 0 := mt (weight_zero_iff f).mp hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  omega

theorem quadratic_min_cost {f : V → F₂} (hf : HasDegreeLE f 2) (hn : f ≠ 0) :
    2 ≤ cost f := by
  have hw := quadratic_min_weight hf hn
  have hb := ZMod.val_lt (f 0)
  unfold cost
  omega

theorem quadratic_even_weight {f : V → F₂} (hf : HasDegreeLE f 2) :
    weight f % 2 = 0 := by
  have hw := quadratic_weights hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  omega

theorem quadratic_small_weight {f : V → F₂} (hf : HasDegreeLE f 2)
    (hn : f ≠ 0) (hw : weight f ≤ 7) : weight f = 4 ∨ weight f = 6 := by
  have hh := quadratic_weights hf
  have hz : weight f ≠ 0 := mt (weight_zero_iff f).mp hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  omega

#print axioms quadratic_weights
#print axioms quadratic_min_cost
end BooleanANF.QuadraticFour
