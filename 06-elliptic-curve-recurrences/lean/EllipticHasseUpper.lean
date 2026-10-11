import EllipticFrobeniusOrbitBound
import EllipticHeightCauchySchwarz

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

open Astra01.EllipticPointDivisor Astra01.EllipticAddSub

local instance : (V⁄F).IsElliptic := inferInstanceAs (V.map (algebraMap F F)).IsElliptic

include k K in
/-- An unconditional upper Hasse discriminant inequality for the actual rational-point count.
All geometric ingredients, including the Frobenius orbit pole bound, are proved locally. -/
theorem rational_count_upper_discriminant :
    (Nat.card (V⁄F).Point : ℤ) - Fintype.card F - 1 ≤ 0 ∨
      ((Nat.card (V⁄F).Point : ℤ) - Fintype.card F - 1)^2 ≤ 4*(Fintype.card F : ℤ) := by
  letI : Algebra F K := ((algebraMap k K).comp (algebraMap F k)).toAlgebra
  let A := geometricGeneric (k := k) V K
  let B := pointFrobenius V K A
  let H := pointHeight (V⁄k) K (V⁄K)
  have hA : H A = 2 := geometricGeneric_height (k := k) V K
  have hB : H B = 2*(Fintype.card F : ℤ) := geometricFrobenius_height (k := k) V K
  have hcount : 2*(Nat.card (V⁄F).Point : ℤ) ≤ H (A-B) :=
    rational_count_le_difference_height (k := k) V K
  have hgeom : H (A-B)-H A-H B ≤ 0 ∨ (H (A-B)-H A-H B)^2 ≤ 4*H A*H B :=
    pointHeight_upper_discriminant (V⁄k) K (V⁄k) A B (by change 0 < H A; rw [hA]; decide)
  rw [hA,hB] at hgeom
  by_cases hn : (Nat.card (V⁄F).Point : ℤ) - Fintype.card F - 1 ≤ 0
  · exact Or.inl hn
  · right
    rcases hgeom with h | h
    · omega
    · let d : ℤ := (Nat.card (V⁄F).Point : ℤ)-Fintype.card F-1
      let t : ℤ := H (A-B)-2-2*Fintype.card F
      have hd : 0 < d := by dsimp [d]; omega
      have ht : 2*d ≤ t := by dsimp [d,t]; omega
      have hprod := mul_nonneg (show 0 ≤ t-2*d by omega) (show 0 ≤ t+2*d by omega)
      change d^2 ≤ 4*(Fintype.card F : ℤ)
      change t^2 ≤ 4*2*(2*(Fintype.card F : ℤ)) at h
      nlinarith

end
end Astra01.EllipticFrobenius
#print axioms Astra01.EllipticFrobenius.rational_count_upper_discriminant
