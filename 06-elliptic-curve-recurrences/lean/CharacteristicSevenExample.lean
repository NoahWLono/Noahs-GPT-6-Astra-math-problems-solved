import ShortCurveYSemiconjugacy
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets

/-! The paper's explicit characteristic-seven global semiconjugacy example,
using actual Weierstrass groups, function fields, pole degree and projective values. -/
namespace Astra01.CharacteristicSeven
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticPointDivisor Astra01.EllipticTranslation
open scoped RatFunc Polynomial
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def baseCurve : WeierstrassCurve.Affine (ZMod 7) := ⟨0, 0, 0, 0, 1⟩
instance : baseCurve.IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  decide

theorem base_equation : baseCurve.Equation 0 1 := by
  rw [baseCurve.equation_iff]
  norm_num [baseCurve]

def basePoint : baseCurve.Point := Point.mk base_equation

theorem base_point_order : addOrderOf basePoint = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply addOrderOf_eq_prime
  · rw [show (3 : ℕ) = 2+1 from rfl, add_nsmul, two_nsmul, one_nsmul]
    have hd : basePoint + basePoint = -basePoint := by
      unfold basePoint Point.mk
      rw [Point.add_self_of_Y_ne (by decide), Point.neg_some]
      congr 1 <;> norm_num [baseCurve, slope, addX, addY, negAddY, negY]
    rw [hd, neg_add_cancel]
  · exact Point.some_ne_zero _

instance (xy : ZMod 7 × ZMod 7) : Decidable (baseCurve.Equation xy.1 xy.2) :=
  decidable_of_iff (xy.2^2 = xy.1^3 + 1) (by rw [baseCurve.equation_iff]; simp [baseCurve])

/-- All rational points of the actual F₇ curve, including infinity, number twelve. -/
theorem base_point_count : Nat.card baseCurve.Point = 12 := by
  rw [Nat.card_congr baseCurve.pointEquiv]
  change Nat.card (Option {xy : ZMod 7 × ZMod 7 // baseCurve.Equation xy.1 xy.2}) = 12
  rw [Nat.card_eq_fintype_card]
  decide

variable (k : Type*) [Field k] [Algebra (ZMod 7) k]
def curve : WeierstrassCurve.Affine k := baseCurve.map (algebraMap (ZMod 7) k)
instance : (curve k).IsElliptic := inferInstanceAs
  (baseCurve.map (algebraMap (ZMod 7) k)).IsElliptic

@[simp] theorem a1 : (curve k).a₁ = 0 := by simp [curve, baseCurve, WeierstrassCurve.map]
@[simp] theorem a2 : (curve k).a₂ = 0 := by simp [curve, baseCurve, WeierstrassCurve.map]
@[simp] theorem a3 : (curve k).a₃ = 0 := by simp [curve, baseCurve, WeierstrassCurve.map]
@[simp] theorem a4 : (curve k).a₄ = 0 := by simp [curve, baseCurve, WeierstrassCurve.map]
@[simp] theorem a6 : (curve k).a₆ = 1 := by simp [curve, baseCurve, WeierstrassCurve.map]

theorem two_ne_zero : (2 : k) ≠ 0 := by
  intro h
  have h2 : (2 : ZMod 7) ≠ 0 := by decide
  apply h2
  exact (algebraMap (ZMod 7) k).injective (by simpa only [map_ofNat, map_zero] using h)

theorem four_ne_zero : (4 : k) ≠ 0 := by
  intro h
  have h4 : (4 : ZMod 7) ≠ 0 := by decide
  apply h4
  exact (algebraMap (ZMod 7) k).injective (by simpa only [map_ofNat, map_zero] using h)

variable [IsAlgClosed k]
local instance : DecidableEq k := Classical.decEq _
def point : (curve k).Point := shortUnitPoint (curve k) (a1 k) (a2 k) (a3 k) (a4 k) (a6 k)

theorem point_order : addOrderOf (point k) = 3 :=
  short_unit_point_order (curve k) (a1 k) (a2 k) (a3 k) (a4 k) (a6 k) (two_ne_zero k)

variable (K : Type*) [Field K] [Algebra (curve k).CoordinateRing K]
  [IsFractionRing (curve k).CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] (curve k).CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K

theorem y_nonconstant : ∀ c : k, (curve k).yCoord K ≠ algebraMap k K c := by
  intro c he
  apply (curve k).yCoord_notMem_range K
  refine ⟨algebraMap k[X] k⟮X⟯ (Polynomial.C c), ?_⟩
  rw [← IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K]
  exact he.symm

theorem rational_pair_coprime :
    IsCoprime (Polynomial.X - Polynomial.C (3 : k)) (Polynomial.X + Polynomial.C (1 : k)) := by
  have h : IsUnit ((3 : k) - (-1)) := isUnit_iff_ne_zero.mpr (by
    convert four_ne_zero k using 1 <;> ring)
  simpa using Polynomial.isCoprime_X_sub_C_of_isUnit_sub h

/-- E3: exact order three, degree three, and the global projective recurrence.
The source and rational map are the explicit ones from the manuscript. -/
theorem characteristic_seven_global_example :
    addOrderOf (point k) = 3 ∧
    divisorDegree (curve k) (poleDivisor (curve k) K (yCoordinateUnit (curve k) K)) = 3 ∧
    ∀ P : (curve k).Point,
      projectiveValue (curve k) K ((curve k).yCoord K) (P + point k) =
        rationalProjectiveMap (Polynomial.X - Polynomial.C (3 : k))
          (Polynomial.X + Polynomial.C (1 : k))
          (projectiveValue (curve k) K ((curve k).yCoord K) P) := by
  refine ⟨point_order k, pole_degree_y (curve k) K, ?_⟩
  intro P
  let p : k[X] := Polynomial.X - Polynomial.C 3
  let q : k[X] := Polynomial.X + Polynomial.C 1
  have hp : p ≠ 0 := by
    intro h
    have hd : p.natDegree = 1 := Polynomial.natDegree_X_sub_C _
    simp [h] at hd
  have hq : q ≠ 0 := by
    intro h
    have hd : q.natDegree = 1 := by
      have he : q = Polynomial.X - Polynomial.C (-1 : k) := by simp [q]
      rw [he]; exact Polynomial.natDegree_X_sub_C _
    simp [h] at hd
  have he := short_y_semiconjugacy (curve k) (a1 k) (a2 k) (a3 k) (a4 k) (a6 k) K
  rw [← projectiveValue_translation (curve k) K (point k) P]
  change projectiveValue (curve k) K (translationEquiv (curve k) K
    (shortUnitPoint (curve k) (a1 k) (a2 k) (a3 k) (a4 k) (a6 k)) ((curve k).yCoord K)) P = _
  rw [he]
  have hc := projectiveValue_rational_composition (curve k) K ((curve k).yCoord K)
    (y_nonconstant k K) p q hp hq (rational_pair_coprime k) P
  simpa [p, q, map_ofNat] using hc

end
end Astra01.CharacteristicSeven
#print axioms Astra01.CharacteristicSeven.base_point_order
#print axioms Astra01.CharacteristicSeven.base_point_count
#print axioms Astra01.CharacteristicSeven.characteristic_seven_global_example
