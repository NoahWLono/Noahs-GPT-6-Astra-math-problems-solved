import EllipticFiberDegree
import FunctionFieldPlaceAction

/-! Exact divisor covariance and pole-degree invariance for actual elliptic
function-field automorphisms. The point permutation here is constructed from
valuation pullback and the point/place bijection. Identifying it with P + G
for translation automorphisms is a separate, still open local-coordinate bridge. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K

def pointPullbackEquiv (e : K ≃ₐ[k] K) : W.Point ≃ W.Point :=
  (pointPlaceEquiv W K).trans ((chartPullbackEquiv e).trans (pointPlaceEquiv W K).symm)

theorem principalDivisor_pullback (e : K ≃ₐ[k] K) (f : Kˣ) (P : W.Point) :
    principalDivisor W K (Additive.ofMul (Units.map e.toMonoidHom f)) P =
      principalDivisor W K (Additive.ofMul f) (pointPullbackEquiv W K e P) := by
  rw [principalDivisor_apply, principalDivisor_apply]
  have h := principalDivisorA_pullback e f (placeOfPoint W K P)
  convert h using 1
  change principalDivisorA k K (Additive.ofMul f)
    ((pointPlaceEquiv W K) ((pointPlaceEquiv W K).symm
      (chartPullbackEquiv e (pointPlaceEquiv W K P)))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem poleDivisor_pullback (e : K ≃ₐ[k] K) (f : Kˣ) :
    poleDivisor W K (Units.map e.toMonoidHom f) =
      (poleDivisor W K f).mapDomain (pointPullbackEquiv W K e).symm := by
  ext P
  have hm := Finsupp.mapDomain_apply (pointPullbackEquiv W K e).symm.injective
    (poleDivisor W K f) (pointPullbackEquiv W K e P)
  rw [Equiv.symm_apply_apply] at hm
  rw [hm]
  simp only [poleDivisor, Finsupp.mapRange_apply, principalDivisor_pullback]

/-- Pole degree is preserved by every actual constant-field automorphism. -/
theorem pole_degree_automorphism (e : K ≃ₐ[k] K) (f : Kˣ) :
    divisorDegree W (poleDivisor W K (Units.map e.toMonoidHom f)) =
      divisorDegree W (poleDivisor W K f) := by
  rw [poleDivisor_pullback]
  unfold divisorDegree
  rw [Finsupp.sum_mapDomain_index (fun _ => (rfl : (0 : ℕ) = 0)) (fun _ _ _ => rfl)]

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.principalDivisor_pullback
#print axioms Astra01.EllipticPointDivisor.pole_degree_automorphism
