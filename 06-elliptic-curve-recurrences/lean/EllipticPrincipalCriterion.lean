import EllipticPrincipalFiniteCoefficients

/-! Actual principal divisors on the projective curve: the coefficient at infinity
is forced by the already proved global product formula. -/
namespace Astra01.EllipticPicard
noncomputable section
attribute [-instance] OreLocalization.instSMulOfIsScalarTower
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticPlaces
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
local instance (priority := 2000) : DecidableEq k := Classical.decEq _
local instance (priority := 2000) : Algebra k[X] W.FunctionField := W.algebraPolynomial W.FunctionField
local instance (priority := 2000) : IsScalarTower k[X] W.CoordinateRing W.FunctionField := W.algebraPolynomial_isScalarTower W.FunctionField
local instance (priority := 2000) : Algebra k⟮X⟯ W.FunctionField := W.algebraRatFunc W.FunctionField
local instance (priority := 2000) : IsScalarTower k[X] k⟮X⟯ W.FunctionField := W.algebraRatFunc_isScalarTower W.FunctionField
local instance (priority := 2000) : _root_.FunctionField k W.FunctionField := W.functionField W.FunctionField
local instance (priority := 2000) : Algebra.IsSeparable k⟮X⟯ W.FunctionField := W.isSeparable W.FunctionField

theorem principal_of_degree_zero_pointSum_zero (D : W.Point →₀ ℤ)
    (hdeg : D.sum (fun _ n => n) = 0) (hsum : pointSum W D = 0) :
    ∃ f : W.FunctionFieldˣ,
      EllipticPointDivisor.principalDivisor W W.FunctionField (Additive.ofMul f) = D := by
  classical
  obtain ⟨f,hf⟩ := affine_principal_of_pointSum_zero W D hsum
  refine ⟨f, ?_⟩
  let A := EllipticPointDivisor.principalDivisor W W.FunctionField (Additive.ofMul f)
  have ha : ∀ {x y : k} (h : W.Nonsingular x y), A (Point.some x y h) = D (Point.some x y h) := by
    intro x y h
    rw [principalDivisor_finite, hf, affineDivisor_apply]
  have he : A - D = Finsupp.single (0 : W.Point) ((A - D) 0) := by
    ext P
    cases P with
    | zero => change (A - D) 0 = (Finsupp.single (0 : W.Point) ((A - D) 0)) 0; simp only [Finsupp.single_eq_same]
    | some x y h => simp [ha h]
  have hz : (A - D).sum (fun _ n => n) = 0 := by
    rw [Finsupp.sum_sub_index (fun _ _ _ => rfl)]
    change A.sum (fun _ n => n) - D.sum (fun _ n => n) = 0
    rw [hdeg, EllipticPointDivisor.sum_principalDivisor_eq_zero]
    rfl
  rw [he] at hz
  simp only [Finsupp.sum_single_index] at hz
  have he0 : A - D = 0 := by rw [he, hz, Finsupp.single_zero]
  exact sub_eq_zero.mp he0
end
end Astra01.EllipticPicard
#print axioms Astra01.EllipticPicard.principal_of_degree_zero_pointSum_zero
