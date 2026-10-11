import EllipticPlaceDictionary

/-! Principal divisors on the actual elliptic-curve point type. The
point/place equivalence is constructed, including the unique infinity place.
This transports the checked product formula to the unweighted sum of
point multiplicities over algebraically closed constants. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine.Chart FunctionField.Chart
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

def principalDivisor : Additive Kˣ →+ (W.Point →₀ ℤ) :=
  (Finsupp.mapDomain.addMonoidHom (pointPlaceEquiv W K).symm).comp
    (principalDivisorA k K)

theorem principalDivisor_apply (f : Additive Kˣ) (P : W.Point) :
    principalDivisor W K f P = principalDivisorA k K f (placeOfPoint W K P) := by
  change (Finsupp.mapDomain (pointPlaceEquiv W K).symm (principalDivisorA k K f)) P =
    principalDivisorA k K f (pointPlaceEquiv W K P)
  have h := Finsupp.mapDomain_apply (pointPlaceEquiv W K).symm.injective
    (principalDivisorA k K f) (pointPlaceEquiv W K P)
  simpa only [Equiv.symm_apply_apply] using h

theorem point_valuation_eq (f : Additive Kˣ) (P : W.Point) :
    placeValuation k K (placeOfPoint W K P) (f.toMul : K) =
      WithZero.exp (-(principalDivisor W K f P)) := by
  rw [principalDivisor_apply]
  exact placeValuation_eq_exp_neg_principalDivisor k K f _

/-- Genuine global principal-divisor product formula, indexed by curve points. -/
theorem sum_principalDivisor_eq_zero (f : Kˣ) :
    (principalDivisor W K (Additive.ofMul f)).sum (fun _ n => n) = 0 := by
  classical
  change (Finsupp.mapDomain (pointPlaceEquiv W K).symm
    (principalDivisorA k K (Additive.ofMul f))).sum (fun _ n => n) = 0
  rw [Finsupp.sum_mapDomain_index (fun _ => (rfl : (0 : ℤ) = 0))
    (fun _ _ _ => rfl)]
  have hd : ∀ v : PlaceA k K, placeDegree k K v = 1 := by
    intro v
    obtain ⟨P,rfl⟩ := placeOfPoint_surjective W K v
    exact placeOfPoint_deg_one W K P
  simpa only [FunctionField.Chart.deg, hd, Nat.cast_one, mul_one] using
    deg_principalDivisorA_eq_zero k K f

#print axioms sum_principalDivisor_eq_zero
#print axioms point_valuation_eq
end
end Astra01.EllipticPointDivisor
