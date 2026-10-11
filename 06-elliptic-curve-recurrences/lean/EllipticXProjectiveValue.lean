import EllipticXYDegrees
import RationalProjectiveComposition

/-! Geometric projective evaluation of the actual x function equals the
ordinary finite x coordinate, with infinity at the elliptic identity. -/
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

def coordinateXValue : W.Point → Option k
  | .zero => none
  | .some x _ _ => some x

theorem projectiveValue_x (P : W.Point) :
    projectiveValue W K (XK k K) P = coordinateXValue W P := by
  cases P with
  | zero =>
    apply (projectiveValue_eq_none_iff W K (XK k K) 0).mpr
    have hp := congrArg (fun d : W.Point →₀ ℕ => d 0) (poleDivisor_x W K)
    simp only [poleDivisor, Finsupp.mapRange_apply, Finsupp.single_eq_same] at hp
    change 1 < placeValuation k K (placeOfPoint W K 0) (xCoordinateUnit W K : K)
    rw [point_valuation_unit W K, ← WithZero.exp_zero]
    apply WithZero.exp_lt_exp.mpr
    omega
  | some x y h =>
    apply (projectiveValue_eq_some_iff W K (XK k K) (.some x y h) x).mpr
    exact (finite_point_residues W K h).1

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.projectiveValue_x
