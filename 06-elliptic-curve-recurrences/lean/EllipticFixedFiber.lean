import EllipticTranslationCovariance
import EllipticCompositionDegree
import LinearFractionFixedFiber

/-! Actual fixed-fiber divisor identities for degree-one rational substitution. -/
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


theorem principalDivisor_constant (c : kˣ) :
    principalDivisor W K (Additive.ofMul (Units.map (algebraMap k K) c)) = 0 := by
  ext P
  rw [principalDivisor_apply]
  exact congrArg (fun d : PlaceA k K →₀ ℤ => d (placeOfPoint W K P))
    (principalDivisorA_algebraMap k K c)

theorem principalDivisor_constant_mul (g h : Kˣ) (c : k) (hc : c ≠ 0)
    (hg : (g : K) = algebraMap k K c * (h : K)) :
    principalDivisor W K (Additive.ofMul g) = principalDivisor W K (Additive.ofMul h) := by
  let cu : Kˣ := Units.map (algebraMap k K) (Units.mk0 c hc)
  have hu : g = cu * h := by apply Units.ext; exact hg
  rw [hu]
  change principalDivisor W K (Additive.ofMul cu + Additive.ofMul h) = _
  rw [map_add, principalDivisor_constant, zero_add]

theorem zeroDivisor_constant_mul (g h : Kˣ) (c : k) (hc : c ≠ 0)
    (hg : (g : K) = algebraMap k K c * (h : K)) :
    zeroDivisor W K g = zeroDivisor W K h := by
  unfold zeroDivisor
  rw [principalDivisor_constant_mul W K g h c hc hg]

theorem zeroDivisor_eq_poleDivisor_inv (f : Kˣ) : zeroDivisor W K f = poleDivisor W K f⁻¹ := by
  have hi := (principalDivisor W K).map_neg (Additive.ofMul f)
  change principalDivisor W K (Additive.ofMul f⁻¹) = -principalDivisor W K (Additive.ofMul f) at hi
  ext P
  simp only [zeroDivisor, poleDivisor, Finsupp.mapRange_apply, hi, Finsupp.neg_apply, neg_neg]

theorem zeroDivisor_rational_of_degree_le (f g h : Kˣ) (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : IsCoprime p q) (hdeg : q.natDegree ≤ p.natDegree)
    (hg : (g : K) = Polynomial.aeval (f : K) p)
    (hh : (h : K) = Polynomial.aeval (f : K) q) :
    zeroDivisor W K (g / h) = zeroDivisor W K g := by
  rw [zeroDivisor_eq_poleDivisor_inv, inv_div,
    poleDivisor_rational W K f h g q p hq hp hpq.symm hh hg,
    Nat.sub_eq_zero_of_le hdeg, zero_smul, add_zero]

theorem zeroDivisor_linear_fiber (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p : k[X]) (hp : p.natDegree = 1) (hp0 : p ≠ 0) (c : k) (hc : p.eval c = 0) :
    zeroDivisor W K (polynomialValueUnit K f hf p hp0) =
      zeroDivisor W K (Units.mk0 (f - algebraMap k K c) (sub_ne_zero.mpr (hf c))) := by
  obtain ⟨hfactor, hlead⟩ := linear_polynomial_root_factor p hp c hc
  apply zeroDivisor_constant_mul W K _ _ (p.coeff 1) hlead
  change Polynomial.aeval f p = algebraMap k K (p.coeff 1) * (f - algebraMap k K c)
  conv_lhs => rw [hfactor]
  simp only [map_mul, map_sub, Polynomial.aeval_C, Polynomial.aeval_X]

theorem zeroDivisor_constant_polynomial (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (q : k[X]) (hq : q ≠ 0) (hdeg : q.natDegree = 0) :
    zeroDivisor W K (polynomialValueUnit K f hf q hq) = 0 := by
  have he := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hc : q.coeff 0 ≠ 0 := by intro h; exact hq (he.trans (by rw [h, Polynomial.C_0]))
  have hu : polynomialValueUnit K f hf q hq = Units.map (algebraMap k K) (Units.mk0 (q.coeff 0) hc) := by
    apply Units.ext
    change Polynomial.aeval f q = algebraMap k K (q.coeff 0)
    conv_lhs => rw [he]
    exact Polynomial.aeval_C _ _
  unfold zeroDivisor
  rw [hu, principalDivisor_constant]
  rfl

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.zeroDivisor_rational_of_degree_le
#print axioms Astra01.EllipticPointDivisor.zeroDivisor_linear_fiber
