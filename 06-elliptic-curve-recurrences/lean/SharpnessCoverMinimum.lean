import EllipticXProjectiveValue
import ProjectiveRecurrenceBounds

/-! Universal lower bound of four degree-one maps to cover an order-thirteen
cyclic orbit under the genuine geometric x function. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open scoped RatFunc Polynomial Polynomial.Bivariate
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : DecidableEq k := Classical.decEq _

theorem cyclicPoints_card (G : W.Point) : (cyclicPoints W G).card = addOrderOf G := by
  rw [cyclicPoints, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    exact Fin.ext (nsmul_injOn_Iio_addOrderOf i.isLt j.isLt hij)

include K in
theorem x_order_thirteen_cover_minimum {ι : Type*} [Fintype ι]
    (G : W.Point) (hG : addOrderOf G = 13)
    (p q : ι → k[X]) (hq : ∀ j, q j ≠ 0) (hpq : ∀ j, IsCoprime (p j) (q j))
    (hdegree : ∀ j, max (p j).natDegree (q j).natDegree = 1)
    (hcover : ∀ P ∈ cyclicPoints W G, ∃ j,
      coordinateXValue W (P+G) = rationalProjectiveMap (p j) (q j) (coordinateXValue W P)) :
    4 ≤ Fintype.card ι := by
  have hf : ∀ c : k, XK k K ≠ algebraMap k K c :=
    EllipticTranslation.generic_x_ne_constant W K
  have hb := full_menu_agreement_set_bound W K G 13 (by decide) hG (XK k K) hf
    p q hq hpq (fun j => by rw [hdegree j])
  have he : ((cyclicPoints W G).filter fun P => ∃ j,
      projectiveValue W K (XK k K) (P+G) =
        rationalProjectiveMap (p j) (q j) (projectiveValue W K (XK k K) P)) =
      cyclicPoints W G := by
    apply Finset.filter_eq_self.mpr
    intro P hP
    simpa only [projectiveValue_x] using hcover P hP
  rw [he, cyclicPoints_card, hG] at hb
  have hunit : Units.mk0 (XK k K) (by simpa using hf 0) = xCoordinateUnit W K := rfl
  rw [hunit, pole_degree_x] at hb
  simp only [hdegree, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hb
  omega

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.x_order_thirteen_cover_minimum
