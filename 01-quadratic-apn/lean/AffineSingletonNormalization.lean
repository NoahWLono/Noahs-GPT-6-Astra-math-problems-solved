import SingletonFlat
import BooleanANFLinear

namespace BooleanANF
open scoped BigOperators

/-- Affine coordinate selection preserves both canonical degree and actual support weight. -/
theorem exists_degree_four_singleton_coordinates (f : EightSpace → F₂)
    (hf : HasDegreeLE f 4) (hw : weight f = 30) :
    ∃ (p : EightSpace) (e : DoubleBlock ≃ₗ[F₂] EightSpace),
      HasDegreeLE (fun z => f (p + e z)) 4 ∧
      weight (fun z => f (p + e z)) = 30 ∧
      fiber (fun z => f (p + e z)) 0 = delta 0 := by
  obtain ⟨p,e,he⟩ := exists_singleton_coordinates f hw
  refine ⟨p,e,hf.comp_linear_translate e.toLinearMap p,?_,he⟩
  have hweight := weight_equiv f (e.toEquiv.trans (Equiv.addLeft p))
  exact hweight.trans hw

/-- Complete normalization entry point for the specialized weight-thirty classification.
The later quadratic-row classification receives all its actual-function hypotheses here. -/
theorem quartic_thirty_normalization (f : EightSpace → F₂)
    (hf : HasDegreeLE f 4) (hw : weight f = 30) :
    ∃ (p : EightSpace) (e : DoubleBlock ≃ₗ[F₂] EightSpace),
      let g : DoubleBlock → F₂ := fun z => f (p + e z)
      HasDegreeLE g 4 ∧ weight g = 30 ∧
      HasDegreeLE (residual g) 4 ∧
      (∀ y : Block, HasDegreeLE (fiber (residual g) y) 2) ∧
      (Finset.univ.filter (fun y : Block => fiber (residual g) y ≠ 0)).card ≤ 7 ∧
      (∑ y : Block, cost (fiber (residual g) y)) = 14 ∧
      (∀ x : Block, (∑ y : Block, fiber (residual g) y x) =
        ∑ y : Block, fiber (residual g) y 0) := by
  obtain ⟨p,e,hdeg,hweight,hsingle⟩ := exists_degree_four_singleton_coordinates f hf hw
  let g : DoubleBlock → F₂ := fun z => f (p + e z)
  refine ⟨p,e,hdeg,hweight,residual_degree hdeg,?_,?_,?_,?_⟩
  · intro y
    rw [residual_fiber]
    exact normalized_residual_quadratic g y (top_one_of_singleton hdeg 0 0 hsingle y)
  · exact residual_active_count hdeg hweight 0 0 hsingle
  · exact residual_cost_fourteen hweight
  · exact residual_sum_constant hdeg

end BooleanANF
