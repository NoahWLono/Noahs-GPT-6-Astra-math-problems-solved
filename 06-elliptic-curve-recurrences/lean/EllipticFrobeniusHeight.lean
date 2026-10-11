import EllipticHeightPowers
import EllipticFrobenius

namespace Astra01.EllipticHeight
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField.Chart
open Astra01.EllipticPointDivisor
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq K := Classical.decEq _

variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

theorem pointHeight_frobenius (V : WeierstrassCurve.Affine F) (A : (V⁄K).Point) :
    pointHeight W K (V⁄K) (EllipticFrobenius.pointFrobenius V K A) =
      Fintype.card F • pointHeight W K (V⁄K) A := by
  simpa only [pointHeight, EllipticFrobenius.pointFrobenius_xRep] using
    vectorHeight_pow W K A.xRep A.xRep_ne_zero (Fintype.card F)

end
end Astra01.EllipticHeight
#print axioms Astra01.EllipticHeight.pointHeight_frobenius
