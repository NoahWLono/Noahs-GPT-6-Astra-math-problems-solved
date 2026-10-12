import NormalizedParameterField
import ReducedAdjoinCoordinates
import AlgebraicPowerPropagation
import GenericBinomialDescent

/-!
# Concrete parameter-prime C1 and C2

The auxiliary field, degree p, full integral closure and faithful integral-order
map are the actual constructions in NormalizedParameterField. The arithmetic
statements assume none of these facts, coefficient integrality or coordinate
uniqueness. The stronger wrappers also derive global binomial irreducibility.
-/

set_option autoImplicit false

open Algebra Polynomial PillaiParameterField

noncomputable section

namespace PillaiLocalCoefficients

universe v

/-! ## Direct lifting into the actual finite integral quotient -/

/-- The inverse of the actual order equivalence lifts every integral element.
This avoids forming or reducing G(c*T^r) before the finite-order descent. -/
lemma normalized_order_lift_of_integral
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime]
    (a : ℕ) (u : ℤ_[ell]ˣ)
    (γ : NormalizedField ell p a u) (hγ : IsIntegral ℤ_[ell] γ) :
    ∃ x : AdjoinRoot (normalizedPolynomial ell p a u),
      normalizedOrderMap ell p a u x = γ := by
  have hmem : γ ∈ adjoin ℤ_[ell]
      ({pi ell p a u} : Set (NormalizedField ell p a u)) := by
    rw [← normalized_integralClosure ell p a u]
    exact hγ
  let z : adjoin ℤ_[ell]
      ({pi ell p a u} : Set (NormalizedField ell p a u)) := ⟨γ, hmem⟩
  refine ⟨(normalizedOrderEquiv ell p a u).symm z, ?_⟩
  change (((normalizedOrderEquiv ell p a u)
    ((normalizedOrderEquiv ell p a u).symm z)) : NormalizedField ell p a u) = γ
  simp only [AlgEquiv.apply_symm_apply]
  rfl

/-- Integrality and the field equation produce the equation in the literal
finite quotient. The only transfer step is the proved injectivity of its map. -/
lemma normalized_order_affine_lift
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime]
    (a : ℕ) (u : ℤ_[ell]ˣ) (r b q : ℕ) (A : ℤ)
    (γ : NormalizedField ell p a u) (hγ : IsIntegral ℤ_[ell] γ)
    (heq : γ ^ q = (A : NormalizedField ell p a u) - localRoot ell p a u r b) :
    ∃ x : PillaiParameterC.Order (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p,
      normalizedOrderMap ell p a u x = γ ∧
      x ^ q =
        PillaiParameterC.scalar (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p (A : ℤ_[ell]) -
        PillaiParameterC.scalar (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p
          ((↑(u⁻¹) : ℤ_[ell]) ^ b) *
        PillaiParameterC.tau (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p ^ r := by
  obtain ⟨x, hx⟩ := normalized_order_lift_of_integral ell p a u γ hγ
  refine ⟨x, hx, ?_⟩
  apply normalizedOrderMap_injective ell p a u
  change normalizedOrderMap ell p a u (x ^ q) =
    normalizedOrderMap ell p a u
      (algebraMap ℤ_[ell] (AdjoinRoot (normalizedPolynomial ell p a u)) (A : ℤ_[ell]) -
        algebraMap ℤ_[ell] (AdjoinRoot (normalizedPolynomial ell p a u))
          ((↑(u⁻¹) : ℤ_[ell]) ^ b) *
            AdjoinRoot.root (normalizedPolynomial ell p a u) ^ r)
  rw [map_pow, hx, map_sub, normalizedOrderMap_localRoot, AlgHom.commutes, map_intCast]
  exact heq

/-- Membership descends through an explicit D-polynomial representative, with
no coordinate uniqueness or extension-field embedding hypothesis. -/
lemma normalized_smaller_order_map_mem
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime]
    (a : ℕ) (u : ℤ_[ell]ˣ) (r b : ℕ)
    (x : PillaiParameterC.Order (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p)
    (hx : x ∈ adjoin ℤ_[ell]
      ({PillaiParameterC.scalar (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p
          ((↑(u⁻¹) : ℤ_[ell]) ^ b) *
        PillaiParameterC.tau (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p ^ r} :
        Set (PillaiParameterC.Order (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p))) :
    normalizedOrderMap ell p a u x ∈ adjoin ℤ_[ell]
      ({localRoot ell p a u r b} : Set (NormalizedField ell p a u)) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx ⊢
  obtain ⟨H, hH⟩ := hx
  refine ⟨H, ?_⟩
  have hs : normalizedOrderMap ell p a u
      (PillaiParameterC.scalar (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p
          ((↑(u⁻¹) : ℤ_[ell]) ^ b) *
        PillaiParameterC.tau (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p ^ r) =
      localRoot ell p a u r b := normalizedOrderMap_localRoot ell p a u r b
  calc
    aeval (localRoot ell p a u r b) H =
        normalizedOrderMap ell p a u
          (aeval (PillaiParameterC.scalar (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p
              ((↑(u⁻¹) : ℤ_[ell]) ^ b) *
            PillaiParameterC.tau (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a) p ^ r) H) := by
      change aeval (localRoot ell p a u r b) H =
        normalizedOrderMap ell p a u
          (aeval (algebraMap ℤ_[ell] (AdjoinRoot (normalizedPolynomial ell p a u))
            ((↑(u⁻¹) : ℤ_[ell]) ^ b) *
            AdjoinRoot.root (normalizedPolynomial ell p a u) ^ r) H)
      rw [← aeval_algHom_apply, normalizedOrderMap_localRoot]
    _ = normalizedOrderMap ell p a u x := congrArg (normalizedOrderMap ell p a u) hH

/-! ## C1: an actual reduced integral polynomial, and coefficient integrality -/

/-- Natural parameter-prime polynomial lift, retaining the scalar-unit result.
The parameter prime ell is allowed to equal p. -/
theorem parameter_prime_polynomial_lift_of_power_equation
    (ell p q : ℕ) [Fact ell.Prime]
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hellq : ell ≠ q)
    (r : ℕ) (hr0 : 0 < r) (hrp : r < p)
    (k U A : ℤ) (hk : k = (ell : ℤ) ^ r * U) (hU : ¬ (ell : ℤ) ∣ U)
    {L : Type v} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ) :
    (¬ (ell : ℤ) ∣ A) ∧
      ∃ H : ℤ_[ell][X], H.natDegree < p ∧
        H.map (algebraMap ℤ_[ell] ℚ_[ell]) = G.map (algebraMap ℚ ℚ_[ell]) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, _, hab⟩ := exists_normalizing_exponents p r hp hr0 hrp
  let u : ℤ_[ell]ˣ := integerUnit ell U hU
  have hu : (u : ℤ_[ell]) = (U : ℤ_[ell]) := integerUnit_val ell U hU
  let t : NormalizedField ell p a u := localRoot ell p a u r b
  have ht : t ^ p = (k : NormalizedField ell p a u) :=
    localRoot_power_int ell p a u r b hab k U hu hk
  have htInt : IsIntegral ℤ_[ell] t := localRoot_isIntegral ell p a u r b
  have hlocal : (aeval t G) ^ q = (A : NormalizedField ell p a u) - t :=
    power_equation_at_root p q k A θ hθ hirr G heq t ht
  have hγInt : IsIntegral ℤ_[ell] (aeval t G) :=
    isIntegral_of_integer_power_equation q hq.pos A (aeval t G) t htInt hlocal
  obtain ⟨x, hx, hxpow⟩ := normalized_order_affine_lift
    ell p a u r b q A (aeval t G) hγInt hlocal
  have hqnotdvd : ¬ (ell : ℤ) ∣ (q : ℤ) := by
    intro hdvd
    have hdvd' : ell ∣ q := Int.natCast_dvd_natCast.mp hdvd
    exact hellq ((hq.dvd_iff_eq (Fact.out : ell.Prime).ne_one).mp hdvd').symm
  have hqUnit : IsUnit (q : ℤ_[ell]) := by
    simpa only [Int.cast_natCast] using int_isUnit_of_not_dvd ell (q : ℤ) hqnotdvd
  have hcop : p.Coprime r := Nat.coprime_of_lt_prime (Nat.ne_of_gt hr0) hrp hp
  obtain ⟨hAunit, hxmem⟩ := PillaiParameterC.dvr_affine_power_root_descent
    (ell : ℤ_[ell]) ((u : ℤ_[ell]) ^ a)
    PadicInt.irreducible_p (u.isUnit.pow a) hr0 hrp hpq.le hcop
    ((u⁻¹) ^ b) (A : ℤ_[ell]) x hxpow hqUnit
  have hAnotdvd : ¬ (ell : ℤ) ∣ A := by
    intro hdiv
    exact (PadicInt.not_isUnit_iff.mpr
      ((PadicInt.norm_int_lt_one_iff_dvd A).mpr hdiv)) hAunit
  have hmem : aeval t G ∈ adjoin ℤ_[ell] ({t} : Set (NormalizedField ell p a u)) := by
    rw [← hx]
    exact normalized_smaller_order_map_mem ell p a u r b x hxmem
  let f : ℤ_[ell][X] := X ^ p - C (k : ℤ_[ell])
  have hf : f.Monic := monic_X_pow_sub_C _ hp.ne_zero
  have hfdeg : f.natDegree = p := natDegree_X_pow_sub_C
  have hfpos : 0 < f.natDegree := by rw [hfdeg]; exact hp.pos
  have hroot : aeval t f = 0 := by
    simp only [f, map_sub, map_pow, aeval_X, map_intCast, ht, sub_self]
  have hminDeg : (minpoly ℚ_[ell] t).natDegree = f.natDegree := by
    rw [hfdeg]
    exact localRoot_minpoly_natDegree ell p a u r b hab
  let GK : ℚ_[ell][X] := G.map (algebraMap ℚ ℚ_[ell])
  have hGKdeg : GK.natDegree < f.natDegree := by
    rw [hfdeg]
    exact lt_of_le_of_lt natDegree_map_le hG
  have hGKmem : aeval t GK ∈ adjoin ℤ_[ell] ({t} : Set (NormalizedField ell p a u)) := by
    simpa only [GK, aeval_map_algebraMap] using hmem
  obtain ⟨H, hHdeg, hH⟩ := PillaiParameterCoordinates.reduced_polynomial_lift_of_adjoin
    (R := ℤ_[ell]) (K := ℚ_[ell]) t f hf hfpos hroot hminDeg GK hGKdeg hGKmem
  exact ⟨hAnotdvd, H, by simpa only [hfdeg] using hHdeg, hH⟩

/-- C1: the affine equation forces ell ∤ A and all reduced rational coefficients
into Z_ell. There are no integrality, local degree, or coordinate assumptions. -/
theorem parameter_prime_coefficients_of_power_equation
    (ell p q : ℕ) [Fact ell.Prime]
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hellq : ell ≠ q)
    (r : ℕ) (hr0 : 0 < r) (hrp : r < p)
    (k U A : ℤ) (hk : k = (ell : ℤ) ^ r * U) (hU : ¬ (ell : ℤ) ∣ U)
    {L : Type v} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ) :
    (¬ (ell : ℤ) ∣ A) ∧
      ∀ j : ℕ, ∃ z : ℤ_[ell],
        algebraMap ℤ_[ell] ℚ_[ell] z = (G.coeff j : ℚ_[ell]) := by
  obtain ⟨hA, H, _, hH⟩ := parameter_prime_polynomial_lift_of_power_equation
    ell p q hp hq hpq hellq r hr0 hrp k U A hk hU θ hθ hirr G hG heq
  refine ⟨hA, fun j => ⟨H.coeff j, ?_⟩⟩
  have hc := congrArg (fun P : ℚ_[ell][X] => P.coeff j) hH
  simpa only [coeff_map, eq_ratCast] using hc

/-! ## C2: the exponent prime divides the parameter -/

/-- C2: the finite quotient's Frobenius obstruction excludes the affine qth
power equation when the parameter prime is q. No scalar-unit assumption is
needed. The stronger statement does not even require G to be reduced. -/
theorem no_power_equation_at_exponent_parameter
    (p q : ℕ) [Fact q.Prime] (hp : p.Prime) (hpq : p < q)
    (r : ℕ) (hr0 : 0 < r) (hrp : r < p)
    (k U A : ℤ) (hk : k = (q : ℤ) ^ r * U) (hU : ¬ (q : ℤ) ∣ U)
    {L : Type v} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (heq : (aeval θ G) ^ q = (A : L) - θ) : False := by
  letI : Fact p.Prime := ⟨hp⟩
  have hq : q.Prime := Fact.out
  obtain ⟨a, b, _, hab⟩ := exists_normalizing_exponents p r hp hr0 hrp
  let u : ℤ_[q]ˣ := integerUnit q U hU
  have hu : (u : ℤ_[q]) = (U : ℤ_[q]) := integerUnit_val q U hU
  let t : NormalizedField q p a u := localRoot q p a u r b
  have ht : t ^ p = (k : NormalizedField q p a u) :=
    localRoot_power_int q p a u r b hab k U hu hk
  have htInt : IsIntegral ℤ_[q] t := localRoot_isIntegral q p a u r b
  have hlocal : (aeval t G) ^ q = (A : NormalizedField q p a u) - t :=
    power_equation_at_root p q k A θ hθ hirr G heq t ht
  have hγInt : IsIntegral ℤ_[q] (aeval t G) :=
    isIntegral_of_integer_power_equation q hq.pos A (aeval t G) t htInt hlocal
  obtain ⟨x, _, hxpow⟩ := normalized_order_affine_lift
    q p a u r b q A (aeval t G) hγInt hlocal
  exact PillaiParameterC.no_affine_prime_power_at_parameter
    q p r hq hpq.le PadicInt.p_nonunit hr0 hrp
    ((u : ℤ_[q]) ^ a) ((↑(u⁻¹) : ℤ_[q]) ^ b) (A : ℤ_[q])
    ((u⁻¹).isUnit.pow b) x hxpow

/-! ## Optional strengthening: derive global irreducibility from normalization -/

/-- The same actual normalized field also proves the rational binomial
irreducible; it is not an additional global hypothesis in the wrappers below. -/
theorem rational_binomial_irreducible_of_parameter_normalization
    (ell p : ℕ) [Fact ell.Prime] (hp : p.Prime)
    (r : ℕ) (hr0 : 0 < r) (hrp : r < p)
    (k U : ℤ) (hk : k = (ell : ℤ) ^ r * U) (hU : ¬ (ell : ℤ) ∣ U) :
    Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, _, hab⟩ := exists_normalizing_exponents p r hp hr0 hrp
  let u : ℤ_[ell]ˣ := integerUnit ell U hU
  have hu : (u : ℤ_[ell]) = (U : ℤ_[ell]) := integerUnit_val ell U hU
  have hlocal : Irreducible ((X : ℚ_[ell][X]) ^ p - C (k : ℚ_[ell])) := by
    rw [localRoot_binomial_eq_minpoly ell p a u r b hab k U hu hk]
    exact minpoly.irreducible ((localRoot_isIntegral ell p a u r b).tower_top)
  apply Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective
    (algebraMap ℚ ℚ_[ell]).injective (monic_X_pow_sub_C (k : ℚ) hp.ne_zero).isPrimitive
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_intCast, map_intCast] using hlocal

/-- Normalization-only C1: global irreducibility is now derived as well. -/
theorem parameter_prime_coefficients_of_normalized_power_equation
    (ell p q : ℕ) [Fact ell.Prime]
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hellq : ell ≠ q)
    (r : ℕ) (hr0 : 0 < r) (hrp : r < p)
    (k U A : ℤ) (hk : k = (ell : ℤ) ^ r * U) (hU : ¬ (ell : ℤ) ∣ U)
    {L : Type v} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ) :
    (¬ (ell : ℤ) ∣ A) ∧
      ∀ j : ℕ, ∃ z : ℤ_[ell],
        algebraMap ℤ_[ell] ℚ_[ell] z = (G.coeff j : ℚ_[ell]) :=
  parameter_prime_coefficients_of_power_equation ell p q hp hq hpq hellq r hr0 hrp
    k U A hk hU θ hθ
    (rational_binomial_irreducible_of_parameter_normalization ell p hp r hr0 hrp k U hk hU)
    G hG heq

/-- Normalization-only C2; no global irreducibility or reducedness input. -/
theorem no_normalized_power_equation_at_exponent_parameter
    (p q : ℕ) [Fact q.Prime] (hp : p.Prime) (hpq : p < q)
    (r : ℕ) (hr0 : 0 < r) (hrp : r < p)
    (k U A : ℤ) (hk : k = (q : ℤ) ^ r * U) (hU : ¬ (q : ℤ) ∣ U)
    {L : Type v} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (G : ℚ[X]) (heq : (aeval θ G) ^ q = (A : L) - θ) : False :=
  no_power_equation_at_exponent_parameter p q hp hpq r hr0 hrp k U A hk hU θ hθ
    (rational_binomial_irreducible_of_parameter_normalization q p hp r hr0 hrp k U hk hU)
    G heq

end PillaiLocalCoefficients
