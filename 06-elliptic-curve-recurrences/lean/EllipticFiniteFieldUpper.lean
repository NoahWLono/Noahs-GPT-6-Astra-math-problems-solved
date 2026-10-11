import EllipticHasseUpper
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Finite-field-only upper Hasse discriminant theorem. The algebraic closure,
coordinate-ring fraction field and every auxiliary field instance are constructed here. -/
namespace Astra01.EllipticFrobenius
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField.Chart
open scoped RatFunc Polynomial
variable {F : Type*} [Field F] [Fintype F]

theorem finite_field_upper_discriminant (V : WeierstrassCurve.Affine F) [V.IsElliptic] :
    (Nat.card V.Point : ℤ) - Fintype.card F - 1 ≤ 0 ∨
      ((Nat.card V.Point : ℤ) - Fintype.card F - 1)^2 ≤ 4*(Fintype.card F : ℤ) := by
  let k := AlgebraicClosure F
  let W := V⁄k
  letI : W.IsElliptic := inferInstanceAs (V.map (algebraMap F k)).IsElliptic
  let K := FractionRing W.CoordinateRing
  letI := W.algebraPolynomial K
  letI := W.algebraPolynomial_isScalarTower K
  letI := W.algebraRatFunc K
  letI := W.algebraRatFunc_isScalarTower K
  letI := W.functionField K
  letI := W.isSeparable K
  exact rational_count_upper_discriminant (k := k) V K

end
end Astra01.EllipticFrobenius
#print axioms Astra01.EllipticFrobenius.finite_field_upper_discriminant
