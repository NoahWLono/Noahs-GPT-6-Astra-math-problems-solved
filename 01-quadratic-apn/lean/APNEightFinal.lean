import APNTwoFlatExclusion
import QuadraticComponentIndicator
import QuadraticSemantics
import BooleanANFQuadraticSix
import WeightThirtyClassification

/-! Unconditional eight-dimensional quadratic APN component bound.
The weight-thirty classification and low-weight residue theorem are actual
checked dependencies, not arguments or axioms of the final statements. -/
namespace APNRedo
open scoped Classical

/-- The exceptional count twenty-nine is impossible for an actual quadratic APN
map: its singular-component indicator has weight thirty and the classified
support contradicts the checked APN rank geometry. -/
theorem apn_degenerate_count_ne_twenty_nine
    (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q) :
    (degenerateLabels Q).card ≠ 29 := by
  intro hcard
  have hw : BooleanANF.weight (componentSingularIndicator Q) = 30 := by
    rw [component_indicator_weight, hcard]
  obtain ⟨e,c,hc,hs⟩ := BooleanANF.quartic_weight_thirty_nonzero_support_profile
    (componentSingularIndicator Q) (component_indicator_degree Q) hw
    (component_indicator_zero Q)
  apply apn_profile29_excluded_by_two_flat_support Q hQ hcard e c hc
  intro a v
  have hh := hs a v
  simpa only [degenerateLabels, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
    and_true, true_and, component_indicator_one_iff, and_comm] using hh

/-- Every actual quadratic APN map in eight dimensions has at least thirty-three
nonzero components with degenerate polar. No classification premise remains. -/
theorem apn_degenerate_count_ge_thirty_three
    (Q : QuadraticMap F (V 8) (V 8)) (hQ : APN Q) :
    33 ≤ (degenerateLabels Q).card := by
  have hmod := apn_degenerate_count_congruence Q hQ
  have hw := component_indicator_weight Q
  have hres : BooleanANF.weight (componentSingularIndicator Q) % 4 = 2 := by omega
  have hmin := BooleanANF.quartic_eight_residue_bound (component_indicator_degree Q) hres
  have hne := apn_degenerate_count_ne_twenty_nine Q hQ
  omega

/-- The same bound counts actual Walsh non-bent components, including arbitrary
constant terms and the linear terms permitted by characteristic-two quadratics. -/
theorem apn_nonBent_count_ge_thirty_three
    (Q : QuadraticMap F (V 8) (V 8)) (c : V 8) (hQ : APN Q) :
    33 ≤ (nonBentLabels Q c).card := by
  rw [nonBentLabels_eq_degenerateLabels]
  exact apn_degenerate_count_ge_thirty_three Q hQ

/-- Direct binary encoding of an arbitrary vectorial function. -/
def encodedFunction (f : V 8 → V 8) : BitVec 8 → BitVec 8 :=
  fun x => QuadraticWalshMatrix.decode (f (QuadraticWalshMatrix.coords x))

/-- Actual nonzero coordinate masks whose scalar components are not Walsh bent. -/
noncomputable def nonBentFunctionLabels (f : V 8 → V 8) : Finset (V 8) :=
  (Finset.univ.erase 0).filter fun b =>
    ¬FastWalsh.IsBent (encodedFunction f) (QuadraticWalshMatrix.decode b)

theorem nonBentFunctionLabels_normalization (f : V 8 → V 8)
    (B : V 8 →ₗ[F] V 8 →ₗ[F] V 8)
    (hB : ∀ x y, normalizedPolar f x y = B x y) :
    nonBentFunctionLabels f = nonBentLabels (quadraticMapOfBilinearPolar f B hB) (f 0) := by
  have he : encodedQuadraticAffine (quadraticMapOfBilinearPolar f B hB) (f 0) =
      encodedFunction f := by
    funext x
    unfold encodedQuadraticAffine encodedFunction
    congr 1
    exact quadraticMapOfBilinearPolar_reconstruct f B hB _
  simp only [nonBentFunctionLabels, nonBentLabels, he]

/-- Function-level form of the bound. Quadraticity is witnessed by bilinearity
of the function's actual normalized polar; APN and bentness are their actual
function/Walsh definitions, with no formal rank proxy in the conclusion. -/
theorem quadratic_apn_function_nonBent_count_ge_thirty_three
    (f : V 8 → V 8)
    (hquad : ∃ B : V 8 →ₗ[F] V 8 →ₗ[F] V 8,
      ∀ x y, normalizedPolar f x y = B x y)
    (hf : APN f) : 33 ≤ (nonBentFunctionLabels f).card := by
  obtain ⟨B,hB⟩ := hquad
  rw [nonBentFunctionLabels_normalization f B hB]
  exact apn_nonBent_count_ge_thirty_three (quadraticMapOfBilinearPolar f B hB) (f 0)
    (quadraticMapOfBilinearPolar_apn f B hB hf)

#print axioms apn_degenerate_count_ne_twenty_nine
#print axioms apn_degenerate_count_ge_thirty_three
#print axioms apn_nonBent_count_ge_thirty_three
#print axioms quadratic_apn_function_nonBent_count_ge_thirty_three
end APNRedo
