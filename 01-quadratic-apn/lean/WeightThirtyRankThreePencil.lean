import WeightThirtyCaseThree
import WeightThirtyCommonRadical
import CodeRadicalCoordinates
import NormalizedCostBudget
import WeightThirtyTypeBTransport

namespace BooleanANF
open QuadraticFour

theorem codeEvaluation_nonzero_iff {q : DoubleBlock → F₂}
    (e : SimplexIndex ≃ₗ[F₂] quadraticCoefficientSpace q) (y : Block) :
    codeEvaluation e y ≠ 0 ↔ y ∈ coefficientRows q := by
  rw [codeBasisWord_detects_rows e y]
  simp [codeEvaluation, funext_iff, not_forall]

/-- The actual dimension-three pencil admits simultaneous radical coordinates,
with one linear equivalence relating code labels and radical lines. -/
theorem NormalizedQuartic.three_pencil_coordinates {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 3) :
    ∃ (e : SimplexIndex ≃ₗ[F₂] quadraticCoefficientSpace q)
      (p : Block) (L : SimplexIndex →ₗ[F₂] Block)
      (ex : Block ≃ₗ[F₂] Block) (R : SimplexIndex ≃ₗ[F₂] SimplexIndex),
      Function.Injective L ∧
      (∀ v, v ≠ 0 → ∀ y, codeEvaluation e y = v ↔ y = p + L v) ∧
      (∀ v, v ≠ 0 → ∀ x,
        fiber q (p+L v) (ex x) = if dropLast x = 0 ∨ dropLast x = R v then 1 else 0) := by
  obtain ⟨e,p,L,hL,hcoord⟩ := h.three_code_affine_coordinates hd
  obtain ⟨r,hr,_⟩ := h.common_radical_all_rows hd
  obtain ⟨ex,hex⟩ := last_coordinate_of_nonzero r r.property
  let R := codeRadicalVectorLinear e ex.toLinearMap
  have hsize : (coefficientRows q).card = 7 :=
    (coefficientSpace_dimension_three h.totalDegree h.activeBound hd).1
  have hcost := normalized_seven_cost_two h hsize
  have hy (v : SimplexIndex) (hv : v ≠ 0) : codeEvaluation e (p+L v) = v :=
    (hcoord v hv (p+L v)).mpr rfl
  have hvec (v : SimplexIndex) (hv : v ≠ 0) :
      radicalVector (fun x => fiber q (p+L v) (ex x)) = R v := by
    have hh := radicalVector_code_expansion e ex.toLinearMap (p+L v) (h.rowDegree (p+L v))
    change radicalVector (fun x => fiber q (p+L v) (ex x)) = R (codeEvaluation e (p+L v)) at hh
    rw [hy v hv] at hh
    exact hh
  have hshape (v : SimplexIndex) (hv : v ≠ 0) :
      R v ≠ 0 ∧ ∀ x, fiber q (p+L v) (ex x) =
        if dropLast x = 0 ∨ dropLast x = R v then 1 else 0 := by
    have hm : p+L v ∈ coefficientRows q :=
      (codeEvaluation_nonzero_iff e _).mp (by rw [hy v hv]; exact hv)
    have hdeg : HasDegreeLE (fun x => fiber q (p+L v) (ex x)) 2 :=
      (h.rowDegree _).comp_linear ex.toLinearMap
    have hc : cost (fun x => fiber q (p+L v) (ex x)) = 2 := by
      rw [cost_linearEquiv]
      exact hcost _ hm
    have hlast : IsRadical (fun x => fiber q (p+L v) (ex x)) lastBasis := by
      intro x
      have hh := polar_comp_linear (fiber q (p+L v)) ex.toLinearMap lastBasis x
      change polar (fun z => fiber q (p+L v) (ex z)) lastBasis x =
        polar (fiber q (p+L v)) (ex lastBasis) (ex x) at hh
      rw [hh, hex]
      exact hr (p+L v) (ex x)
    have hs := cost_two_last_radical_shape hdeg hc hlast
    simpa only [hvec v hv] using hs
  have hinj : Function.Injective R := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_cases hz : v=0
    · exact hz
    · exact False.elim ((hshape v hz).1 hv)
  let Re : SimplexIndex ≃ₗ[F₂] SimplexIndex :=
    LinearEquiv.ofBijective R ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact ⟨e,p,L,ex,Re,hL,hcoord,fun v hv => (hshape v hv).2⟩

end BooleanANF
