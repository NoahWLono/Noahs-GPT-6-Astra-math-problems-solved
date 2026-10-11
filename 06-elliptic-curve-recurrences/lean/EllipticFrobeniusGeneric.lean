import EllipticFrobeniusHeight
import EllipticTranslationCovariance

/-! Frobenius and rational translations specialized to the genuine generic
point of the geometric function field of a finite-field elliptic curve. -/
namespace Astra01.EllipticFrobenius
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField.Chart
open Astra01.EllipticHeight Astra01.EllipticTranslation
open scoped RatFunc Polynomial
variable {F k : Type*} [Field F] [Fintype F] [Field k] [IsAlgClosed k] [Algebra F k]
variable (V : WeierstrassCurve.Affine F) [V.IsElliptic]
local instance : (V⁄k).IsElliptic := inferInstanceAs (V.map (algebraMap F k)).IsElliptic
variable (K : Type*) [Field K] [Algebra (V⁄k).CoordinateRing K]
  [IsFractionRing (V⁄k).CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] (V⁄k).CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : DecidableEq F := Classical.decEq _
local instance : DecidableEq k := Classical.decEq _
local instance : DecidableEq K := Classical.decEq _

/-- The genuine generic point, viewed on the original finite-field base change. -/
def geometricGeneric :
    letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra;
    (V⁄K).Point := by
  letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra;
  exact genericPoint (V⁄k) K

theorem geometricGeneric_height :
    letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra;
    pointHeight (V⁄k) K (V⁄K) (geometricGeneric V K) = 2 := by
  letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra;
  exact generic_point_height (V⁄k) K

theorem geometricFrobenius_height :
    letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra;
    pointHeight (V⁄k) K (V⁄K) (pointFrobenius V K (geometricGeneric V K)) =
      2 * (Fintype.card F : ℤ) := by
  letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra;
  rw [pointHeight_frobenius, geometricGeneric_height]
  simp [nsmul_eq_mul, mul_comm]

/-- Actual source-curve rational translations fix generic minus Frobenius(generic). -/
theorem geometricDifference_translation (T : (V⁄F).Point) :
    letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra;
    letI : IsScalarTower F k K := IsScalarTower.of_algebraMap_eq (fun _ => rfl);
    Point.map (W' := V)
      ((translationEquiv (V⁄k) K (Point.baseChange F k T)).restrictScalars F).toAlgHom
      (geometricGeneric V K - pointFrobenius V K (geometricGeneric V K)) =
        geometricGeneric V K - pointFrobenius V K (geometricGeneric V K) := by
  letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra;
  letI : IsScalarTower F k K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  apply difference_invariant V K _ _ T
  have h := translationEquiv_generic (V⁄k) K (Point.baseChange F k T)
  cases T <;> exact h

end
end Astra01.EllipticFrobenius
#print axioms Astra01.EllipticFrobenius.geometricFrobenius_height
#print axioms Astra01.EllipticFrobenius.geometricDifference_translation
