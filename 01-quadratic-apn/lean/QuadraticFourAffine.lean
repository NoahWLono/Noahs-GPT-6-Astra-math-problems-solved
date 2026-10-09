import QuadraticFourRadical
import QuadraticFourWeights

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace BooleanANF.QuadraticFour

theorem affine_poly_classification : ∀ a b c d e : F₂,
    poly a b c d e 0 0 0 0 0 0 = 0 ∨
    poly a b c d e 0 0 0 0 0 0 = (fun _ => 1) ∨
    cost (poly a b c d e 0 0 0 0 0 0) = 6 ∨
    cost (poly a b c d e 0 0 0 0 0 0) = 8 := by decide

theorem affine_induction {P : (V → F₂) → Prop} {q : V → F₂}
    (hq : HasDegreeLE q 1)
    (hp : ∀ a b c d e : F₂, P (poly a b c d e 0 0 0 0 0 0)) : P q := by
  have hz5 := hq (indices 5) (by decide)
  have hz6 := hq (indices 6) (by decide)
  have hz7 := hq (indices 7) (by decide)
  have hz8 := hq (indices 8) (by decide)
  have hz9 := hq (indices 9) (by decide)
  have hz10 := hq (indices 10) (by decide)
  rw [← representation (hq.mono (by omega)), eval_eq_poly]
  simp only [hz5,hz6,hz7,hz8,hz9,hz10]
  exact hp _ _ _ _ _

theorem affine_cost_classification {q : V → F₂} (hq : HasDegreeLE q 1) :
    q = 0 ∨ q = (fun _ => 1) ∨ cost q = 6 ∨ cost q = 8 :=
  affine_induction (P := fun q => q = 0 ∨ q = (fun _ => 1) ∨ cost q = 6 ∨ cost q = 8)
    hq affine_poly_classification

theorem affine_nonconstant_cost {q : V → F₂} (hq : HasDegreeLE q 1)
    (h0 : q ≠ 0) (h1 : q ≠ fun _ => 1) : cost q = 6 ∨ cost q = 8 := by
  rcases affine_cost_classification hq with h | h | h
  · exact (h0 h).elim
  · exact (h1 h).elim
  · exact h

theorem cost_const_one : cost (fun _ : V => (1 : F₂)) = 14 := by decide

theorem affine_nonzero_min_cost {q : V → F₂} (hq : HasDegreeLE q 1)
    (h0 : q ≠ 0) : 6 ≤ cost q := by
  rcases affine_cost_classification hq with h | h | h | h
  · exact (h0 h).elim
  · rw [h, cost_const_one]; omega
  · omega
  · omega

theorem radical_one_min_cost {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 1) : 4 ≤ cost q := by
  have hw := radical_one_weights hq hr
  have hb := ZMod.val_lt (q 0)
  unfold cost
  omega

theorem affine_poly_weights : ∀ a b c d e : F₂,
    weight (poly a b c d e 0 0 0 0 0 0) ∈ ({0,8,16} : Finset ℕ) := by decide

theorem affine_weights {q : V → F₂} (hq : HasDegreeLE q 1) :
    weight q ∈ ({0,8,16} : Finset ℕ) :=
  affine_induction (P := fun q => weight q ∈ ({0,8,16} : Finset ℕ)) hq affine_poly_weights

theorem affine_weight_mod_eight {q : V → F₂} (hq : HasDegreeLE q 1) : weight q % 8 = 0 := by
  have hw := affine_weights hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  omega

#print axioms affine_cost_classification
end BooleanANF.QuadraticFour
