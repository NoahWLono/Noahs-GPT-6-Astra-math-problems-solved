import SimplexLabels
import SevenPointAffineCube
import SevenPlaneIncidence
import QuadraticThreeRadicalLine

namespace BooleanANF

/-- Actual dimension-three coefficient rows admit simultaneous affine coordinates.
This proves the geometric support and preserves all coefficient-evaluation labels. -/
theorem NormalizedQuartic.three_code_affine_coordinates {q : DoubleBlock → F₂}
    (h : NormalizedQuartic q)
    (hd : Module.finrank F₂ (quadraticCoefficientSpace q) = 3) :
    ∃ (e : SimplexIndex ≃ₗ[F₂] quadraticCoefficientSpace q)
      (p : Block) (L : SimplexIndex →ₗ[F₂] Block),
      Function.Injective L ∧
      (∀ v, v ≠ 0 → ∀ y, codeEvaluation e y = v ↔ y = p + L v) := by
  obtain ⟨e,label,hl,hm⟩ := exists_simplex_labels h hd
  have hinj : ∀ v w, v ≠ 0 → w ≠ 0 → label v = label w → v = w := by
    intro v w hv hw heq
    have hv' := (hl v hv (label v)).mpr rfl
    have hw' := (hl w hw (label w)).mpr rfl
    rw [heq, hw'] at hv'
    exact hv'.symm
  obtain ⟨p,L,hL,hlabel⟩ := seven_point_embedding_of_moments label hm hinj
  refine ⟨e,p,L,hL,?_⟩
  intro v hv y
  rw [hl v hv y, hlabel v hv]

/-- The omitted point has zero evaluation column, so it is genuinely the missing
point of the affine three-flat rather than an additional active row. -/
theorem code_affine_missing_point {q : DoubleBlock → F₂}
    (e : SimplexIndex ≃ₗ[F₂] quadraticCoefficientSpace q)
    (p : Block) (L : SimplexIndex →ₗ[F₂] Block) (hinj : Function.Injective L)
    (hcoord : ∀ v, v ≠ 0 → ∀ y, codeEvaluation e y = v ↔ y = p + L v) :
    codeEvaluation e p = 0 := by
  by_cases hz : codeEvaluation e p = 0
  · exact hz
  have heq := (hcoord (codeEvaluation e p) hz p).mp rfl
  have hzero : L (codeEvaluation e p) = L 0 := by
    rw [map_zero]
    exact add_left_cancel (show p + L (codeEvaluation e p) = p + 0 by simpa using heq.symm)
  exact hinj hzero

end BooleanANF
