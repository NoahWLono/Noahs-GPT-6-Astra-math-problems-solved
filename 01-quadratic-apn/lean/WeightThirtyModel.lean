import QuadraticCoefficientCode
import BooleanANFAffine

namespace BooleanANF
open scoped BigOperators

/-- Exact hypotheses already derived by the checked normalization theorem. -/
structure NormalizedQuartic (q : DoubleBlock → F₂) : Prop where
  totalDegree : HasDegreeLE q 4
  rowDegree : ∀ y : Block, HasDegreeLE (fiber q y) 2
  activeBound : (activeRows q).card ≤ 7
  costFourteen : (∑ y : Block, cost (fiber q y)) = 14
  sumConstant : ∀ x : Block, (∑ y : Block, fiber q y x) = ∑ y : Block, fiber q y 0

def residualSignal (q : DoubleBlock → F₂) (z : DoubleBlock) : F₂ :=
  delta 0 (fun i => z (.inl i)) + q z

/-- Two transverse affine four-flats, expressed by a genuine linear coordinate equivalence.
Their common point is p; the indicator sum is their symmetric difference. -/
def TwoTransverseFlats {V : Type*} [AddCommGroup V] [Module F₂ V] (f : V → F₂) : Prop :=
  ∃ (p : V) (e : DoubleBlock ≃ₗ[F₂] V),
    ∀ x y : Block, f (p + e (Sum.elim x y)) = delta 0 x + delta 0 y

theorem TwoTransverseFlats.of_affine_coordinates {V : Type*}
    [AddCommGroup V] [Module F₂ V] (f : V → F₂) (p₀ : V)
    (e₀ : DoubleBlock ≃ₗ[F₂] V)
    (h : TwoTransverseFlats (fun z => f (p₀ + e₀ z))) : TwoTransverseFlats f := by
  obtain ⟨p,e,he⟩ := h
  refine ⟨p₀ + e₀ p, e.trans e₀, ?_⟩
  intro x y
  simpa only [LinearEquiv.trans_apply, map_add, add_assoc] using he x y

@[simp] theorem residualSignal_residual (f : DoubleBlock → F₂) :
    residualSignal (residual f) = normalized f := by
  funext z
  simp only [residualSignal, residual]
  rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]

theorem TwoTransverseFlats.of_normalized {f : DoubleBlock → F₂}
    (hf : HasDegreeLE f 4) (h : TwoTransverseFlats (normalized f)) :
    TwoTransverseFlats f := by
  obtain ⟨e,he⟩ := shearMap_affine_coordinates hf
  have hn : normalized f = fun z => f (shearMap f 0 + e z) := by
    funext z
    exact congrArg f (he z)
  rw [hn] at h
  exact TwoTransverseFlats.of_affine_coordinates f (shearMap f 0) e h

/-- The code dimension is a derived invariant of the normalized model. -/
theorem NormalizedQuartic.code_dimension {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q) : Module.finrank F₂ (quadraticCoefficientSpace q) ≤ 3 :=
  quadraticCoefficientSpace_finrank h.totalDegree h.activeBound

/-- Transfer a completed normalized classification back to the original quartic.
This is an assembly lemma, not an assumed or claimed classification theorem. -/
theorem transfer_normalized_classification
    (classify : ∀ q : DoubleBlock → F₂, NormalizedQuartic q → TwoTransverseFlats (residualSignal q))
    (f : EightSpace → F₂) (hf : HasDegreeLE f 4) (hw : weight f = 30) :
    TwoTransverseFlats f := by
  obtain ⟨p,e,hdeg,hweight,hsingle⟩ := exists_degree_four_singleton_coordinates f hf hw
  let g : DoubleBlock → F₂ := fun z => f (p + e z)
  have hq : NormalizedQuartic (residual g) :=
    { totalDegree := residual_degree hdeg
      rowDegree := fun y => normalized_residual_quadratic g y
        (top_one_of_singleton hdeg 0 0 hsingle y)
      activeBound := residual_active_count hdeg hweight 0 0 hsingle
      costFourteen := residual_cost_fourteen hweight
      sumConstant := residual_sum_constant hdeg }
  have hh := classify (residual g) hq
  rw [residualSignal_residual] at hh
  exact TwoTransverseFlats.of_affine_coordinates f p e (hh.of_normalized hdeg)

end BooleanANF
