import SharpnessGeometricAgreements

/-! Explicit four-map cover and universal minimum-four conclusion for E2. -/
namespace Astra01.SharpnessActual
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticPointDivisor Polynomial
open scoped RatFunc Polynomial
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
variable (k : Type*) [Field k] [Algebra (ZMod 11) k]
local instance : DecidableEq k := Classical.decEq _

def menuB : Fin 4 → ZMod 11 := ![4,3,10,1]
def menuC : Fin 4 → ZMod 11 := ![7,6,10,5]
def menuD : Fin 4 → ZMod 11 := ![8,9,0,6]
def menuP (j : Fin 4) : k[X] := X+C (algebraMap (ZMod 11) k (menuB j))
def menuQ (j : Fin 4) : k[X] :=
  C (algebraMap (ZMod 11) k (menuC j))*X+C (algebraMap (ZMod 11) k (menuD j))

theorem menuC_ne_zero (j : Fin 4) : algebraMap (ZMod 11) k (menuC j) ≠ 0 := by
  exact (_root_.map_ne_zero (algebraMap (ZMod 11) k)).mpr (by revert j; decide)

theorem menu_det_ne_zero (j : Fin 4) :
    algebraMap (ZMod 11) k (menuD j) -
      algebraMap (ZMod 11) k (menuB j)*algebraMap (ZMod 11) k (menuC j) ≠ 0 := by
  rw [← map_mul, ← map_sub]
  exact (_root_.map_ne_zero (algebraMap (ZMod 11) k)).mpr (by revert j; decide)

theorem linear_pair_coprime {l : Type*} [Field l] (b c d : l) (hd : d-b*c ≠ 0) :
    IsCoprime (X+C b) (C c*X+C d) := by
  refine ⟨C (-c/(d-b*c)), C (1/(d-b*c)), ?_⟩
  have he : (-c/(d-b*c))*b + (1/(d-b*c))*d = 1 := by
    calc
      _ = (d-b*c)/(d-b*c) := by ring
      _ = 1 := div_self hd
  calc
    _ = C ((-c/(d-b*c))*b+(1/(d-b*c))*d) := by
      simp only [map_add, map_mul]
      have hz : C (-c/(d-b*c)) + C (1/(d-b*c))*C c = (0 : l[X]) := by
        rw [← map_mul, ← map_add]
        simp only [div_eq_mul_inv, one_mul]
        have h : -c*(d-b*c)⁻¹+(d-b*c)⁻¹*c = 0 := by ring
        rw [h, map_zero]
      linear_combination hz * X
    _ = 1 := by rw [he, map_one]

theorem menuQ_ne_zero (j : Fin 4) : menuQ k j ≠ 0 := by
  intro h
  have hd := natDegree_linear (menuC_ne_zero k j) (b := algebraMap (ZMod 11) k (menuD j))
  change (menuQ k j).natDegree = 1 at hd
  simp [h] at hd

theorem menu_coprime (j : Fin 4) : IsCoprime (menuP k j) (menuQ k j) :=
  linear_pair_coprime _ _ _ (menu_det_ne_zero k j)

theorem menu_degree (j : Fin 4) : max (menuP k j).natDegree (menuQ k j).natDegree = 1 := by
  simp only [menuP, menuQ, natDegree_X_add_C, natDegree_linear (menuC_ne_zero k j), max_self]

theorem menu_covers_extended_point (P : curve.Point) : ∃ j : Fin 4,
    coordinateXValue (extendedCurve k) (extendPoint k P + extendPoint k generator) =
      rationalProjectiveMap (menuP k j) (menuQ k j)
        (coordinateXValue (extendedCurve k) (extendPoint k P)) := by
  rcases extended_four_cover k P with h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩

theorem menu_covers_cyclic (P : (extendedCurve k).Point)
    (hP : P ∈ cyclicPoints (extendedCurve k) (extendPoint k generator)) : ∃ j : Fin 4,
    coordinateXValue (extendedCurve k) (P + extendPoint k generator) =
      rationalProjectiveMap (menuP k j) (menuQ k j) (coordinateXValue (extendedCurve k) P) := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hP
  simpa only [map_nsmul] using menu_covers_extended_point k (i.val • generator)

variable [IsAlgClosed k]
variable (K : Type*) [Field K] [Algebra (extendedCurve k).CoordinateRing K]
  [IsFractionRing (extendedCurve k).CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] (extendedCurve k).CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

include K in
theorem no_smaller_cover {ι : Type*} [Fintype ι]
    (p q : ι → k[X]) (hq : ∀ j, q j ≠ 0) (hpq : ∀ j, IsCoprime (p j) (q j))
    (hdegree : ∀ j, max (p j).natDegree (q j).natDegree = 1)
    (hcover : ∀ P ∈ cyclicPoints (extendedCurve k) (extendPoint k generator), ∃ j,
      coordinateXValue (extendedCurve k) (P+extendPoint k generator) =
        rationalProjectiveMap (p j) (q j) (coordinateXValue (extendedCurve k) P)) :
    4 ≤ Fintype.card ι :=
  x_order_thirteen_cover_minimum (extendedCurve k) K _ (extended_generator_order k)
    p q hq hpq hdegree hcover

end
end Astra01.SharpnessActual
#print axioms Astra01.SharpnessActual.menu_coprime
#print axioms Astra01.SharpnessActual.menu_degree
#print axioms Astra01.SharpnessActual.menu_covers_cyclic
#print axioms Astra01.SharpnessActual.no_smaller_cover
