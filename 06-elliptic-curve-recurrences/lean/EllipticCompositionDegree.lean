import EllipticAutomorphismDivisor
import EllipticTranslation

/-! Pole-degree behavior under genuine polynomial and rational substitution.
The degree here is the already constructed point-divisor pole degree. -/
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

theorem valuation_polynomial_le_one (v : PlaceA k K) (p : k[X]) (f : K)
    (hf : placeValuation k K v f ≤ 1) :
    placeValuation k K v (Polynomial.aeval f p) ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using (placeValuation k K v).map_add_le hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, map_mul, map_pow]
    exact mul_le_one₀ (placeValuation_algebraMap_le_one k K v a) zero_le
      (pow_le_one₀ zero_le hf)

/-- Polynomial substitution multiplies every pole multiplicity by its degree. -/
theorem poleDivisor_polynomial (f g : Kˣ) (p : k[X]) (hp : p ≠ 0)
    (hg : (g : K) = Polynomial.aeval (f : K) p) :
    poleDivisor W K g = p.natDegree • poleDivisor W K f := by
  ext P
  simp only [poleDivisor, Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
  let v := placeValuation k K (placeOfPoint W K P)
  let df := principalDivisor W K (Additive.ofMul f) P
  let dg := principalDivisor W K (Additive.ofMul g) P
  have hfval : v (f : K) = WithZero.exp (-df) := point_valuation_eq W K _ P
  have hgval : v (g : K) = WithZero.exp (-dg) := point_valuation_eq W K _ P
  change (-dg).toNat = p.natDegree * (-df).toNat
  by_cases hd : 0 ≤ df
  · have hfv : v (f : K) ≤ 1 := by
      rw [hfval, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (neg_nonpos.mpr hd)
    have hgv : v (g : K) ≤ 1 := by
      rw [hg]
      exact valuation_polynomial_le_one K _ p _ hfv
    rw [hgval, ← WithZero.exp_zero] at hgv
    have hdg := WithZero.exp_le_exp.mp hgv
    have hf0 : (-df).toNat = 0 := by omega
    have hg0 : (-dg).toNat = 0 := by omega
    rw [hf0, hg0, mul_zero]
  · have hfv : 1 < v (f : K) := by
      rw [hfval, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (neg_pos.mpr (lt_of_not_ge hd))
    letI : v.IsTrivialOn k := Valuation.IsTrivialOn.of_le_one v
      (placeValuation_algebraMap_le_one k K _)
    have hv := Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
      (v := v) (f : K) hfv hp
    rw [← hg, hgval, hfval, ← WithZero.exp_nsmul] at hv
    have he := WithZero.exp_injective hv
    rw [he, nsmul_eq_mul, Int.toNat_mul (by omega) (by omega), Int.toNat_natCast]

theorem pole_degree_polynomial (f g : Kˣ) (p : k[X]) (hp : p ≠ 0)
    (hg : (g : K) = Polynomial.aeval (f : K) p) :
    divisorDegree W (poleDivisor W K g) =
      p.natDegree * divisorDegree W (poleDivisor W K f) := by
  rw [poleDivisor_polynomial W K f g p hp hg]
  unfold divisorDegree
  rw [Finsupp.sum_smul_index (fun _ => rfl)]
  simp only [Finsupp.sum, ← Finset.mul_sum]


/-- Coprime numerator and denominator cannot both vanish at a regular value. -/
theorem valuation_coprime_regular (v : PlaceA k K) (p q : k[X])
    (hpq : IsCoprime p q) (f : K) (hf : placeValuation k K v f ≤ 1) :
    placeValuation k K v (Polynomial.aeval f p) = 1 ∨
      placeValuation k K v (Polynomial.aeval f q) = 1 := by
  by_contra! hn
  have hp := lt_of_le_of_ne (valuation_polynomial_le_one K v p f hf) hn.1
  have hq := lt_of_le_of_ne (valuation_polynomial_le_one K v q f hf) hn.2
  obtain ⟨a, b, hab⟩ := hpq
  have he := congrArg (Polynomial.aeval f : k[X] →ₐ[k] K) hab
  simp only [map_add, map_mul, map_one] at he
  have h1 : placeValuation k K v (Polynomial.aeval f a * Polynomial.aeval f p) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le
      (valuation_polynomial_le_one K v a f hf)) hp
  have h2 : placeValuation k K v (Polynomial.aeval f b * Polynomial.aeval f q) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le
      (valuation_polynomial_le_one K v b f hf)) hq
  have hv := (placeValuation k K v).map_add_lt h1 h2
  rw [he, map_one] at hv
  exact lt_irrefl _ hv

theorem principal_polynomial_at_pole (f g : Kˣ) (p : k[X]) (hp : p ≠ 0)
    (hg : (g : K) = Polynomial.aeval (f : K) p) (P : W.Point)
    (hP : principalDivisor W K (Additive.ofMul f) P < 0) :
    principalDivisor W K (Additive.ofMul g) P =
      (p.natDegree : ℤ) * principalDivisor W K (Additive.ofMul f) P := by
  let v := placeValuation k K (placeOfPoint W K P)
  letI : v.IsTrivialOn k := Valuation.IsTrivialOn.of_le_one v
    (placeValuation_algebraMap_le_one k K _)
  have hfval : v (f : K) = WithZero.exp (-(principalDivisor W K (Additive.ofMul f) P)) :=
    point_valuation_eq W K _ P
  have hgval : v (g : K) = WithZero.exp (-(principalDivisor W K (Additive.ofMul g) P)) :=
    point_valuation_eq W K _ P
  have hfv : 1 < v (f : K) := by
    rw [hfval, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hv := Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
    (v := v) (f : K) hfv hp
  rw [← hg] at hv
  rw [hgval, hfval, ← WithZero.exp_nsmul] at hv
  have he := WithZero.exp_injective hv
  simpa only [nsmul_eq_mul, mul_neg, neg_inj] using he


private theorem negative_multiples (m n : ℕ) (d : ℤ) (hd : d < 0) :
    (-((m : ℤ) * d - (n : ℤ) * d)).toNat = (m - n) * (-d).toNat := by
  rw [show -((m : ℤ) * d - (n : ℤ) * d) = ((m : ℤ) - n) * (-d) by ring]
  by_cases h : n ≤ m
  · rw [← Int.natCast_sub h, Int.toNat_mul (by omega) (by omega), Int.toNat_natCast]
  · have hz : ((m : ℤ) - n) * (-d) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
    rw [Int.toNat_eq_zero.mpr hz, Nat.sub_eq_zero_of_le (by omega), zero_mul]

theorem poleDivisor_rational (f g h : Kˣ) (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : IsCoprime p q)
    (hg : (g : K) = Polynomial.aeval (f : K) p)
    (hh : (h : K) = Polynomial.aeval (f : K) q) :
    poleDivisor W K (g / h) = zeroDivisor W K h +
      (p.natDegree - q.natDegree) • poleDivisor W K f := by
  ext P
  let df := principalDivisor W K (Additive.ofMul f) P
  let dg := principalDivisor W K (Additive.ofMul g) P
  let dh := principalDivisor W K (Additive.ofMul h) P
  have hdiv : principalDivisor W K (Additive.ofMul (g / h)) P = dg - dh := by
    have he := (principalDivisor W K).map_sub (Additive.ofMul g) (Additive.ofMul h)
    exact congrArg (fun d : W.Point →₀ ℤ => d P) he
  simp only [poleDivisor, zeroDivisor, Finsupp.mapRange_apply, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, hdiv]
  change (-(dg - dh)).toNat = dh.toNat + (p.natDegree - q.natDegree) * (-df).toNat
  by_cases hd : df < 0
  · have hgp : dg = (p.natDegree : ℤ) * df := principal_polynomial_at_pole W K f g p hp hg P hd
    have hhp : dh = (q.natDegree : ℤ) * df := principal_polynomial_at_pole W K f h q hq hh P hd
    have hh0 : dh.toNat = 0 := Int.toNat_eq_zero.mpr (by rw [hhp]; exact mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega))
    rw [hh0, zero_add, hgp, hhp]
    exact negative_multiples _ _ df hd
  · let v := placeValuation k K (placeOfPoint W K P)
    have hfval : v (f : K) = WithZero.exp (-df) := point_valuation_eq W K _ P
    have hgval : v (g : K) = WithZero.exp (-dg) := point_valuation_eq W K _ P
    have hhval : v (h : K) = WithZero.exp (-dh) := point_valuation_eq W K _ P
    have hfv : v (f : K) ≤ 1 := by
      rw [hfval, ← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hgp : 0 ≤ dg := by
      have hv : v (g : K) ≤ 1 := hg ▸ valuation_polynomial_le_one K _ p _ hfv
      rw [hgval, ← WithZero.exp_zero] at hv
      have := WithZero.exp_le_exp.mp hv
      omega
    have hhp : 0 ≤ dh := by
      have hv : v (h : K) ≤ 1 := hh ▸ valuation_polynomial_le_one K _ q _ hfv
      rw [hhval, ← WithZero.exp_zero] at hv
      have := WithZero.exp_le_exp.mp hv
      omega
    have hc := valuation_coprime_regular K (placeOfPoint W K P) p q hpq (f : K) hfv
    rw [← hg, ← hh] at hc
    change v (g : K) = 1 ∨ v (h : K) = 1 at hc
    rw [hgval, hhval, ← WithZero.exp_zero] at hc
    have hz : dg = 0 ∨ dh = 0 := hc.imp
      (fun he => by have := WithZero.exp_injective he; omega)
      (fun he => by have := WithZero.exp_injective he; omega)
    have hf0 : (-df).toNat = 0 := by omega
    rw [hf0, mul_zero, add_zero]
    rcases hz with hz | hz <;> omega


/-- The actual rational-map composition-degree formula, for a reduced
numerator/denominator pair and nonzero evaluations. -/
theorem pole_degree_rational (f g h : Kˣ) (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : IsCoprime p q)
    (hg : (g : K) = Polynomial.aeval (f : K) p)
    (hh : (h : K) = Polynomial.aeval (f : K) q) :
    divisorDegree W (poleDivisor W K (g / h)) =
      max p.natDegree q.natDegree * divisorDegree W (poleDivisor W K f) := by
  classical
  rw [poleDivisor_rational W K f g h p q hp hq hpq hg hh]
  unfold divisorDegree
  rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl),
    Finsupp.sum_smul_index (fun _ => rfl)]
  simp only [Finsupp.sum, ← Finset.mul_sum]
  change divisorDegree W (zeroDivisor W K h) +
    (p.natDegree - q.natDegree) * divisorDegree W (poleDivisor W K f) = _
  rw [zero_degree_eq_pole_degree, pole_degree_polynomial W K f h q hq hh, ← Nat.add_mul]
  congr 1
  omega

theorem nonconstant_polynomial_ne_zero (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p : k[X]) (hp : p ≠ 0) : Polynomial.aeval f p ≠ 0 := by
  intro he
  have ha : IsAlgebraic k f := ⟨p, hp, he⟩
  obtain ⟨c, hc⟩ := Astra01.EllipticTranslation.integral_eq_constant K ha.isIntegral
  exact hf c hc.symm

/-- On a nonconstant elliptic function, every nonzero polynomial evaluates
nontrivially; this supplies the units required by divisor theory. -/
def polynomialValueUnit (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p : k[X]) (hp : p ≠ 0) : Kˣ :=
  Units.mk0 (Polynomial.aeval f p) (nonconstant_polynomial_ne_zero K f hf p hp)

/-- No nonzero-evaluation oracle is required: nonconstancy supplies all of them. -/
theorem nonconstant_rational_composition_degree (f : K)
    (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : IsCoprime p q) :
    divisorDegree W (poleDivisor W K
      (polynomialValueUnit K f hf p hp / polynomialValueUnit K f hf q hq)) =
      max p.natDegree q.natDegree * divisorDegree W
        (poleDivisor W K (Units.mk0 f (by simpa using hf 0))) := by
  exact pole_degree_rational W K _ _ _ p q hp hq hpq rfl rfl

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.poleDivisor_polynomial
#print axioms Astra01.EllipticPointDivisor.pole_degree_polynomial

#print axioms Astra01.EllipticPointDivisor.poleDivisor_rational

#print axioms Astra01.EllipticPointDivisor.nonconstant_rational_composition_degree
