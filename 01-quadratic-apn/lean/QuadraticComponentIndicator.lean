import BilinearIndicator
import APNCountCongruence
import BooleanANFWeight
set_option maxHeartbeats 600000
namespace APNRedo
open MatchingDeterminant

/-- The actual singular-component indicator, including the zero component. -/
def componentSingularIndicator (Q : QuadraticMap F (V 8) (V 8)) (b : V 8) : F :=
  1 + formNonsingularIndicator (componentPencil Q b)

theorem component_indicator_degree (Q : QuadraticMap F (V 8) (V 8)) :
    BooleanANF.HasDegreeLE (componentSingularIndicator Q) 4 := by
  exact degree_form_singular_indicator (componentPencil Q)
    (fun b => componentPolarDual_alternating Q (coordinateDotForm 8 b))

theorem component_indicator_one_iff (Q : QuadraticMap F (V 8) (V 8)) (b : V 8) :
    componentSingularIndicator Q b = 1 ↔ ¬Nondegenerate (componentPencil Q b) := by
  have hbit : ∀ a : F, 1+a=1 ↔ a≠1 := by decide
  change (1 + formNonsingularIndicator (componentPencil Q b) = 1) ↔
    ¬LinearMap.BilinForm.Nondegenerate (componentPencil Q b)
  rw [hbit]
  exact not_congr (form_indicator_one_iff _)

theorem component_indicator_zero (Q : QuadraticMap F (V 8) (V 8)) :
    componentSingularIndicator Q 0 = 1 := by
  have hn : ¬LinearMap.BilinForm.Nondegenerate (0 : MatchingDeterminant.Form8) :=
    LinearMap.BilinForm.not_nondegenerate_zero F (V 8)
  have ho : formNonsingularIndicator (0 : MatchingDeterminant.Form8) ≠ 1 := by
    intro hh
    exact hn ((form_indicator_one_iff _).mp hh)
  have hz : formNonsingularIndicator (0 : MatchingDeterminant.Form8) = 0 :=
    (PfaffianEight.binary_zero_or_one _).resolve_right ho
  unfold componentSingularIndicator
  rw [map_zero, hz, add_zero]

/-- Its Hamming weight is exactly one plus the number of degenerate nonzero
components. The zero label is not silently discarded. -/
theorem component_indicator_weight (Q : QuadraticMap F (V 8) (V 8)) :
    BooleanANF.weight (componentSingularIndicator Q) = (degenerateLabels Q).card + 1 := by
  classical
  rw [BooleanANF.weight_eq_support_card]
  let S := Finset.univ.filter (fun b => componentSingularIndicator Q b = 1)
  have hs : S.erase 0 = degenerateLabels Q := by
    ext b
    simp [S, degenerateLabels, component_indicator_one_iff, and_assoc, and_left_comm]
  have hz : (0 : V 8) ∈ S := by simp [S, component_indicator_zero]
  have hc := Finset.card_erase_add_one hz
  rw [hs] at hc
  exact hc.symm

#print axioms component_indicator_degree
#print axioms component_indicator_zero
#print axioms component_indicator_weight
end APNRedo
