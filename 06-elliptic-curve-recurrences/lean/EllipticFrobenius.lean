import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.Basic

/-! Actual finite-field Frobenius on the elliptic point group, including
commutation and invariance of the Frobenius difference under rational translations. -/
namespace Astra01.EllipticFrobenius
noncomputable section
open WeierstrassCurve.Affine
variable {F : Type*} [Field F] [Fintype F]
variable (W : WeierstrassCurve.Affine F)
variable (K : Type*) [Field K] [Algebra F K]
local instance : DecidableEq F := Classical.decEq _
local instance : DecidableEq K := Classical.decEq _

/-- Frobenius is the actual point-group homomorphism induced by q-th powers. -/
def pointFrobenius : (W⁄K).Point →+ (W⁄K).Point :=
  Point.map (W' := W) (FiniteField.frobeniusAlgHom F K)

theorem pointFrobenius_some {x y : K} (h : (W⁄K).Nonsingular x y) :
    pointFrobenius W K (.some x y h) =
      .some (x ^ Fintype.card F) (y ^ Fintype.card F)
        ((W.baseChange_nonsingular (FiniteField.frobeniusAlgHom F K).injective ..).mpr h) := rfl

theorem pointFrobenius_xRep (P : (W⁄K).Point) :
    (pointFrobenius W K P).xRep = fun i => P.xRep i ^ Fintype.card F := by
  cases P with
  | zero =>
    funext i
    fin_cases i <;> simp [pointFrobenius, Point.map, Point.xRep, Fintype.card_pos.ne']
  | some x y h =>
    funext i
    fin_cases i <;> simp [pointFrobenius, Point.map, Point.xRep]

theorem pointFrobenius_rational (T : (W⁄F).Point) :
    pointFrobenius W K (Point.baseChange F K T) = Point.baseChange F K T :=
  Point.map_baseChange (FiniteField.frobeniusAlgHom F K) T

theorem pointFrobenius_commutes (σ : K →ₐ[F] K) (P : (W⁄K).Point) :
    pointFrobenius W K (Point.map σ P) =
      Point.map σ (pointFrobenius W K P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [pointFrobenius, Point.map_some, Point.some.injEq]
    exact ⟨(map_pow σ x _).symm, (map_pow σ y _).symm⟩

/-- If a field automorphism translates an actual point by a rational point,
then it fixes the point minus its Frobenius image. -/
theorem difference_invariant (σ : K →ₐ[F] K) (P : (W⁄K).Point)
    (T : (W⁄F).Point) (hσ : Point.map σ P = P + Point.baseChange F K T) :
    Point.map σ (P - pointFrobenius W K P) = P - pointFrobenius W K P := by
  rw [map_sub, ← pointFrobenius_commutes, hσ, map_add,
    pointFrobenius_rational]
  abel

end
end Astra01.EllipticFrobenius
#print axioms Astra01.EllipticFrobenius.pointFrobenius_rational
#print axioms Astra01.EllipticFrobenius.difference_invariant
