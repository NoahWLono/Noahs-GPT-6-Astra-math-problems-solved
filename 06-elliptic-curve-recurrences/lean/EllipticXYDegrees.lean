import EllipticCoordinatePoleDegree

/-! The standard x and y coordinates have actual pole degrees two and three.
These are universal nonsingular Weierstrass statements in every characteristic. -/
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

include W in
theorem xCoord_ne_zero : XK k K ≠ 0 := by
  simpa using EllipticTranslation.generic_x_ne_constant W K (0 : k)

theorem yCoord_ne_zero : W.yCoord K ≠ 0 := by
  intro hy
  exact W.yCoord_notMem_range K ⟨0, by simpa using hy.symm⟩

def xCoordinateUnit : Kˣ := Units.mk0 (XK k K) (xCoord_ne_zero W K)
def yCoordinateUnit : Kˣ := Units.mk0 (W.yCoord K) (yCoord_ne_zero W K)

theorem coordinate_norm_x_degree :
    (Algebra.norm k[X] (CoordinateRing.mk W (Polynomial.C Polynomial.X))).natDegree = 2 := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  have h := CoordinateRing.degree_norm_smul_basis (W' := W) (Polynomial.X : k[X]) 0
  norm_num [Algebra.smul_def] at h
  exact h

theorem coordinate_norm_y_degree :
    (Algebra.norm k[X] (CoordinateRing.mk W Polynomial.X)).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  have h := CoordinateRing.degree_norm_smul_basis (W' := W) (0 : k[X]) 1
  norm_num at h
  exact h

theorem pole_degree_x : divisorDegree W (poleDivisor W K (xCoordinateUnit W K)) = 2 := by
  rw [pole_degree_coordinate W K (CoordinateRing.mk W (Polynomial.C Polynomial.X))
    (xCoordinateUnit W K) (xCoord_eq_XK W K).symm]
  exact coordinate_norm_x_degree W

theorem pole_degree_y : divisorDegree W (poleDivisor W K (yCoordinateUnit W K)) = 3 := by
  rw [pole_degree_coordinate W K (CoordinateRing.mk W Polynomial.X) (yCoordinateUnit W K) rfl]
  exact coordinate_norm_y_degree W

theorem poleDivisor_x : poleDivisor W K (xCoordinateUnit W K) = Finsupp.single 0 2 := by
  rw [poleDivisor_coordinate W K (CoordinateRing.mk W (Polynomial.C Polynomial.X))
    (xCoordinateUnit W K) (xCoord_eq_XK W K).symm]
  congr 1
  rw [show (xCoordinateUnit W K : K) = algebraMap W.CoordinateRing K
    (CoordinateRing.mk W (Polynomial.C Polynomial.X)) from (xCoord_eq_XK W K).symm,
    field_norm_coordinate, RatFunc.intDegree_polynomial]
  simpa using coordinate_norm_x_degree W

theorem poleDivisor_y : poleDivisor W K (yCoordinateUnit W K) = Finsupp.single 0 3 := by
  rw [poleDivisor_coordinate W K (CoordinateRing.mk W Polynomial.X) (yCoordinateUnit W K) rfl]
  congr 1
  rw [show (yCoordinateUnit W K : K) = algebraMap W.CoordinateRing K
    (CoordinateRing.mk W Polynomial.X) from rfl,
    field_norm_coordinate, RatFunc.intDegree_polynomial]
  simpa using coordinate_norm_y_degree W

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.pole_degree_x
#print axioms Astra01.EllipticPointDivisor.pole_degree_y
#print axioms Astra01.EllipticPointDivisor.poleDivisor_x
#print axioms Astra01.EllipticPointDivisor.poleDivisor_y
