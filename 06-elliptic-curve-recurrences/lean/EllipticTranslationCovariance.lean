import EllipticAuxiliaryPoints
import TranslationActionRigidity

/-! The genuine point permutation induced by translation pullback equals
addition by G at every point, including infinity, doubling, and inverse pairs. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticTranslation
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : DecidableEq k := Classical.decEq _

theorem chart_eq_of_valuation_eq {v w : PlaceA k K}
    (h : placeValuation k K v = placeValuation k K w) : v = w := by
  apply (chartToPlace k K).injective
  apply FunctionField.Place.ext
  rw [← FunctionField.Place.valuationSubring_valuation,
    ← FunctionField.Place.valuationSubring_valuation, placeValuation_eq, placeValuation_eq, h]

theorem pointPullback_place (e : K ≃ₐ[k] K) (P : W.Point) :
    placeOfPoint W K (pointPullbackEquiv W K e P) =
      chartPullbackEquiv e (placeOfPoint W K P) := by
  change (pointPlaceEquiv W K) ((pointPlaceEquiv W K).symm
    (chartPullbackEquiv e (pointPlaceEquiv W K P))) = _
  rw [Equiv.apply_symm_apply]
  rfl

def translationPointEquiv (G : W.Point) : Equiv.Perm W.Point :=
  pointPullbackEquiv W K (translationEquiv W K G)

theorem translationPoint_zero (P : W.Point) : translationPointEquiv W K 0 P = P := by
  apply (pointPlaceEquiv W K).injective
  change placeOfPoint W K (pointPullbackEquiv W K (translationEquiv W K 0) P) = placeOfPoint W K P
  rw [pointPullback_place]
  apply chart_eq_of_valuation_eq K
  ext f
  rw [chartPullback_valuation]
  change placeValuation k K (placeOfPoint W K P) (translationHom W K 0 f) = _
  rw [translationHom_zero]
  rfl

theorem translationPoint_add (G H P : W.Point) :
    translationPointEquiv W K (G + H) P =
      translationPointEquiv W K G (translationPointEquiv W K H P) := by
  apply (pointPlaceEquiv W K).injective
  change placeOfPoint W K (pointPullbackEquiv W K (translationEquiv W K (G + H)) P) =
    placeOfPoint W K (pointPullbackEquiv W K (translationEquiv W K G)
      (pointPullbackEquiv W K (translationEquiv W K H) P))
  simp only [pointPullback_place]
  apply chart_eq_of_valuation_eq K
  ext f
  simp only [chartPullback_valuation]
  change placeValuation k K (placeOfPoint W K P) (translationHom W K (G + H) f) =
    placeValuation k K (placeOfPoint W K P) (translationHom W K H (translationHom W K G f))
  have he := AlgHom.congr_fun (translationHom_add W K H G) f
  rw [add_comm H G] at he
  exact congrArg (placeValuation k K (placeOfPoint W K P)) he.symm

theorem translationPoint_generic (G P : W.Point) (hP : P ≠ 0)
    (hPG : P ≠ G) (hPnG : P ≠ -G) : translationPointEquiv W K G P = P + G := by
  cases G with
  | zero => simpa only [← Point.zero_def, add_zero] using translationPoint_zero W K P
  | some u w hG =>
    cases P with
    | zero => exact False.elim (hP rfl)
    | some x y hP' =>
      have hx : x ≠ u := by
        intro hxu
        obtain hy | hy := W.Y_eq_of_X_eq hP'.1 hG.1 hxu
        · apply hPG
          subst x
          subst y
          rfl
        · apply hPnG
          subst x
          subst y
          rfl
      apply (pointPlaceEquiv W K).injective
      change placeOfPoint W K (pointPullbackEquiv W K (translationEquiv W K (.some u w hG))
        (.some x y hP')) = placeOfPoint W K (.some x y hP' + .some u w hG)
      rw [pointPullback_place]
      exact translation_place_of_x_ne W K hP' hG hx

/-- All exceptional points are included, in every characteristic. -/
theorem translationPoint_eq_add (G P : W.Point) : translationPointEquiv W K G P = P + G :=
  translation_action_rigidity (translationPointEquiv W K) (translationPoint_zero W K)
    (translationPoint_add W K) (translationPoint_generic W K)
    (EllipticPoints.exists_auxiliary W) G P

/-- Principal-divisor covariance under the actual curve translation, with
point labels now identified as addition by G rather than an unnamed permutation. -/
theorem principalDivisor_translation (G P : W.Point) (f : Kˣ) :
    principalDivisor W K (Additive.ofMul (Units.map (translationEquiv W K G).toMonoidHom f)) P =
      principalDivisor W K (Additive.ofMul f) (P + G) := by
  rw [principalDivisor_pullback]
  exact congrArg (principalDivisor W K (Additive.ofMul f)) (translationPoint_eq_add W K G P)

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.translationPoint_eq_add
#print axioms Astra01.EllipticPointDivisor.principalDivisor_translation
