import SharpnessBaseChange
import LinearFractionBaseChange
import SharpnessCoverMinimum

/-! The four-agreement sharpness witness and four-map cover after faithful
base extension, with the genuine geometric projective x function. -/
namespace Astra01.SharpnessActual
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticPointDivisor
open Polynomial
open scoped RatFunc Polynomial
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
variable (k : Type*) [Field k] [Algebra (ZMod 11) k]
local instance : DecidableEq k := Classical.decEq _

def extendedFractionalMap (b c d : ZMod 11) : Option k → Option k :=
  rationalProjectiveMap (X+C (algebraMap (ZMod 11) k b))
    (C (algebraMap (ZMod 11) k c)*X+C (algebraMap (ZMod 11) k d))

theorem extended_agreement_iff (b c d : ZMod 11) (hc : c ≠ 0) (hd : d-b*c ≠ 0)
    (P : curve.Point) :
    coordinateXValue (extendedCurve k) (extendPoint k P + extendPoint k generator) =
      extendedFractionalMap k b c d (coordinateXValue (extendedCurve k) (extendPoint k P)) ↔
    xValue (P+generator) = fractionalMap b c d (xValue P) := by
  rw [← map_add, extended_xValue, extended_xValue]
  exact linearFraction_baseChange_iff (algebraMap (ZMod 11) k) b c d hc hd _ _

theorem extended_exact_indices (i : Fin 13) :
    coordinateXValue (extendedCurve k) (extendPoint k (orbit i) + extendPoint k generator) =
      extendedFractionalMap k 0 1 5 (coordinateXValue (extendedCurve k) (extendPoint k (orbit i))) ↔
      i = 1 ∨ i = 6 ∨ i = 8 ∨ i = 9 := by
  rw [extended_agreement_iff k 0 1 5 (by decide) (by decide)]
  exact exact_agreement_indices i

theorem extended_four_cover (P : curve.Point) :
    coordinateXValue (extendedCurve k) (extendPoint k P + extendPoint k generator) =
      extendedFractionalMap k 4 7 8 (coordinateXValue (extendedCurve k) (extendPoint k P)) ∨
    coordinateXValue (extendedCurve k) (extendPoint k P + extendPoint k generator) =
      extendedFractionalMap k 3 6 9 (coordinateXValue (extendedCurve k) (extendPoint k P)) ∨
    coordinateXValue (extendedCurve k) (extendPoint k P + extendPoint k generator) =
      extendedFractionalMap k 10 10 0 (coordinateXValue (extendedCurve k) (extendPoint k P)) ∨
    coordinateXValue (extendedCurve k) (extendPoint k P + extendPoint k generator) =
      extendedFractionalMap k 1 5 6 (coordinateXValue (extendedCurve k) (extendPoint k P)) := by
  rw [extended_agreement_iff k 4 7 8 (by decide) (by decide),
    extended_agreement_iff k 3 6 9 (by decide) (by decide),
    extended_agreement_iff k 10 10 0 (by decide) (by decide),
    extended_agreement_iff k 1 5 6 (by decide) (by decide)]
  obtain ⟨i,rfl⟩ := orbit_surjective P
  exact actual_four_maps_cover i

variable [IsAlgClosed k]
variable (K : Type*) [Field K] [Algebra (extendedCurve k).CoordinateRing K]
  [IsFractionRing (extendedCurve k).CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] (extendedCurve k).CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

theorem geometric_exact_indices (i : Fin 13) :
    projectiveValue (extendedCurve k) K (XK k K)
        (extendPoint k (orbit i) + extendPoint k generator) =
      extendedFractionalMap k 0 1 5
        (projectiveValue (extendedCurve k) K (XK k K) (extendPoint k (orbit i))) ↔
      i = 1 ∨ i = 6 ∨ i = 8 ∨ i = 9 := by
  simpa only [projectiveValue_x] using extended_exact_indices k i

theorem geometric_exact_count :
    (Finset.univ.filter fun i : Fin 13 =>
      projectiveValue (extendedCurve k) K (XK k K)
          (extendPoint k (orbit i) + extendPoint k generator) =
        extendedFractionalMap k 0 1 5
          (projectiveValue (extendedCurve k) K (XK k K) (extendPoint k (orbit i)))).card = 4 := by
  simp only [geometric_exact_indices]
  decide
end
end Astra01.SharpnessActual
#print axioms Astra01.SharpnessActual.geometric_exact_count
#print axioms Astra01.SharpnessActual.extended_four_cover
