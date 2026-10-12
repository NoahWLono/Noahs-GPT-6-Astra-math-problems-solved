import MonicEisensteinClosure
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.Tactic.Ring

/-!
# The actual normalized parameter-prime extension

The field is literally AdjoinRoot of the mapped polynomial X^p - ell*u^a.
Its field instance comes from a proved Eisenstein irreducibility statement.
The ring polynomial, degree, full integral closure and faithful integral-order map
are derived, rather than hypotheses of the construction.
-/

set_option autoImplicit false

open Algebra Polynomial

noncomputable section

namespace PillaiParameterField

/-! ## Elementary normalization, before any local-field construction -/

/-- Choose nonnegative Bézout coefficients with a positive inverse exponent. -/
theorem exists_normalizing_exponents (p r : ℕ) (hp : p.Prime)
    (hr0 : 0 < r) (hrp : r < p) :
    ∃ a b : ℕ, a < p ∧ a * r = b * p + 1 := by
  have hcop : r.Coprime p :=
    (Nat.coprime_of_lt_prime (Nat.ne_of_gt hr0) hrp hp).symm
  obtain ⟨a, ha, hamod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨a, r * a / p, ha, ?_⟩
  have hdiv := Nat.mod_add_div (r * a) p
  rw [hamod] at hdiv
  calc
    a * r = r * a := Nat.mul_comm _ _
    _ = 1 + p * (r * a / p) := hdiv.symm
    _ = (r * a / p) * p + 1 := by ac_rfl

/-- First normalization identity; the only cancellation is by the unit v. -/
theorem normalized_power_identity {E : Type*} [Field E]
    (p r a b : ℕ) (lam π v : E) (hv : v ≠ 0)
    (hπ : π ^ p = lam * v ^ a) (hab : a * r = b * p + 1) :
    (π ^ r * (v⁻¹) ^ b) ^ p = lam ^ r * v := by
  have hπr : (π ^ r) ^ p = lam ^ r * v ^ (b * p + 1) := by
    calc
      (π ^ r) ^ p = (π ^ p) ^ r := by
        rw [← pow_mul, Nat.mul_comm r p, pow_mul]
      _ = lam ^ r * v ^ (b * p + 1) := by
        rw [hπ, mul_pow, ← pow_mul, hab]
  have hvbp : ((v⁻¹) ^ b) ^ p = (v ^ (b * p))⁻¹ := by
    rw [← pow_mul, inv_pow]
  rw [mul_pow, hπr, hvbp, pow_succ]
  calc
    (lam ^ r * (v ^ (b * p) * v)) * (v ^ (b * p))⁻¹ =
        (lam ^ r * v) * (v ^ (b * p) * (v ^ (b * p))⁻¹) := by ring
    _ = lam ^ r * v := by rw [mul_inv_cancel₀ (pow_ne_zero _ hv), mul_one]

/-- Recovery of the Eisenstein generator from the normalized root. -/
theorem normalized_recovery_identity {E : Type*} [Field E]
    (p r a b : ℕ) (lam π v : E) (hv : v ≠ 0)
    (hπ : π ^ p = lam * v ^ a) (hab : a * r = b * p + 1) :
    (π ^ r * (v⁻¹) ^ b) ^ a = lam ^ b * π := by
  have hπra : (π ^ r) ^ a = lam ^ b * v ^ (a * b) * π := by
    calc
      (π ^ r) ^ a = π ^ (a * r) := by
        rw [← pow_mul, Nat.mul_comm r a]
      _ = π ^ (b * p + 1) := by rw [hab]
      _ = (π ^ p) ^ b * π := by
        rw [pow_succ, ← pow_mul, Nat.mul_comm p b]
      _ = lam ^ b * v ^ (a * b) * π := by
        rw [hπ, mul_pow, ← pow_mul]
  have hvba : ((v⁻¹) ^ b) ^ a = (v ^ (a * b))⁻¹ := by
    rw [← pow_mul, Nat.mul_comm b a, inv_pow]
  rw [mul_pow, hπra, hvba]
  calc
    (lam ^ b * v ^ (a * b) * π) * (v ^ (a * b))⁻¹ =
        (lam ^ b * π) * (v ^ (a * b) * (v ^ (a * b))⁻¹) := by ring
    _ = lam ^ b * π := by rw [mul_inv_cancel₀ (pow_ne_zero _ hv), mul_one]

/-! ## The actual unit and actual Eisenstein polynomial -/

variable (ell : ℕ) [Fact ell.Prime]

lemma int_isUnit_of_not_dvd (U : ℤ) (hU : ¬ (ell : ℤ) ∣ U) :
    IsUnit (U : ℤ_[ell]) := by
  apply PadicInt.isUnit_iff.mpr
  apply le_antisymm (PadicInt.norm_le_one _)
  apply le_of_not_gt
  exact fun h => hU ((PadicInt.norm_int_lt_one_iff_dvd U).mp h)

/-- The normalized scalar unit is made from the supplied integer U. -/
def integerUnit (U : ℤ) (hU : ¬ (ell : ℤ) ∣ U) : ℤ_[ell]ˣ :=
  (int_isUnit_of_not_dvd ell U hU).unit

@[simp] lemma integerUnit_val (U : ℤ) (hU : ¬ (ell : ℤ) ∣ U) :
    (integerUnit ell U hU : ℤ_[ell]) = (U : ℤ_[ell]) :=
  (int_isUnit_of_not_dvd ell U hU).unit_spec

def normalizedPolynomial (p a : ℕ) (u : ℤ_[ell]ˣ) : ℤ_[ell][X] :=
  X ^ p - C ((ell : ℤ_[ell]) * (u : ℤ_[ell]) ^ a)

lemma normalizedPolynomial_monic (p a : ℕ) (u : ℤ_[ell]ˣ) (hp : p ≠ 0) :
    (normalizedPolynomial ell p a u).Monic :=
  monic_X_pow_sub_C _ hp

lemma normalizedPolynomial_natDegree (p a : ℕ) (u : ℤ_[ell]ˣ) :
    (normalizedPolynomial ell p a u).natDegree = p :=
  natDegree_X_pow_sub_C

/-- The normalized binomial is Eisenstein even when ell = p. -/
lemma normalizedPolynomial_eisenstein (p a : ℕ) (u : ℤ_[ell]ˣ) (hp : p ≠ 0) :
    (normalizedPolynomial ell p a u).IsEisensteinAt
      (Ideal.span {(ell : ℤ_[ell])}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(normalizedPolynomial_monic ell p a u hp).leadingCoeff,
      Ideal.mem_span_singleton]
    intro h
    exact PadicInt.p_nonunit (isUnit_iff_dvd_one.mpr h)
  · intro j hj
    rw [normalizedPolynomial_natDegree] at hj
    rw [Ideal.mem_span_singleton]
    have hpj : p ≠ j := (Nat.ne_of_lt hj).symm
    by_cases hj0 : j = 0
    · subst j
      change (ell : ℤ_[ell]) ∣ ((X : ℤ_[ell][X]) ^ p -
        C ((ell : ℤ_[ell]) * (u : ℤ_[ell]) ^ a)).coeff 0
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hp.symm, if_pos rfl, zero_sub]
      exact dvd_neg.mpr (dvd_mul_right _ _)
    · change (ell : ℤ_[ell]) ∣ ((X : ℤ_[ell][X]) ^ p -
        C ((ell : ℤ_[ell]) * (u : ℤ_[ell]) ^ a)).coeff j
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hpj.symm, if_neg hj0, sub_self]
      exact dvd_zero _
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    have hnot : ¬ (ell : ℤ_[ell]) ^ 2 ∣
        -((ell : ℤ_[ell]) * (u : ℤ_[ell]) ^ a) := by
      intro h
      have hdiv : (ell : ℤ_[ell]) ^ 2 ∣
          (ell : ℤ_[ell]) * (u : ℤ_[ell]) ^ a := dvd_neg.mp h
      rw [pow_two] at hdiv
      have hunitdiv : (ell : ℤ_[ell]) ∣ (u : ℤ_[ell]) ^ a :=
        (mul_dvd_mul_iff_left PadicInt.irreducible_p.ne_zero).mp hdiv
      exact PadicInt.irreducible_p.not_dvd_isUnit (u.isUnit.pow a) hunitdiv
    change ¬ (ell : ℤ_[ell]) ^ 2 ∣ ((X : ℤ_[ell][X]) ^ p -
      C ((ell : ℤ_[ell]) * (u : ℤ_[ell]) ^ a)).coeff 0
    rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hp.symm, if_pos rfl, zero_sub]
    exact hnot

lemma normalizedPolynomial_irreducible (p a : ℕ) (u : ℤ_[ell]ˣ) (hp : p ≠ 0) :
    Irreducible (normalizedPolynomial ell p a u) := by
  have hprime : (Ideal.span {(ell : ℤ_[ell])}).IsPrime := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  apply (normalizedPolynomial_eisenstein ell p a u hp).irreducible hprime
    (normalizedPolynomial_monic ell p a u hp).isPrimitive
  rw [normalizedPolynomial_natDegree]
  exact Nat.pos_of_ne_zero hp

def fieldPolynomial (p a : ℕ) (u : ℤ_[ell]ˣ) : ℚ_[ell][X] :=
  (normalizedPolynomial ell p a u).map (algebraMap ℤ_[ell] ℚ_[ell])

lemma fieldPolynomial_irreducible (p a : ℕ) (u : ℤ_[ell]ˣ) (hp : p ≠ 0) :
    Irreducible (fieldPolynomial ell p a u) :=
  (normalizedPolynomial_monic ell p a u hp).irreducible_iff_irreducible_map_fraction_map.mp
    (normalizedPolynomial_irreducible ell p a u hp)

/-! ## The field and its two explicit generators -/

variable (p : ℕ) [Fact p.Prime]

/-- This instance is a theorem consequence, not an irreducibility input. -/
instance fieldPolynomial_irreducibleFact (a : ℕ) (u : ℤ_[ell]ˣ) :
    Fact (Irreducible (fieldPolynomial ell p a u)) :=
  ⟨fieldPolynomial_irreducible ell p a u (Fact.out : p.Prime).ne_zero⟩

/-- Literal quotient construction; mathlib supplies its field from the preceding Fact. -/
abbrev NormalizedField (a : ℕ) (u : ℤ_[ell]ˣ) :=
  AdjoinRoot (fieldPolynomial ell p a u)

/-- The actual Eisenstein power basis. -/
def normalizedPowerBasis (a : ℕ) (u : ℤ_[ell]ˣ) :
    PowerBasis ℚ_[ell] (NormalizedField ell p a u) :=
  AdjoinRoot.powerBasis
    (fieldPolynomial_irreducible ell p a u (Fact.out : p.Prime).ne_zero).ne_zero

def pi (a : ℕ) (u : ℤ_[ell]ˣ) : NormalizedField ell p a u :=
  AdjoinRoot.root (fieldPolynomial ell p a u)

lemma normalizedPowerBasis_gen (a : ℕ) (u : ℤ_[ell]ˣ) :
    (normalizedPowerBasis ell p a u).gen = pi ell p a u := rfl

lemma normalizedPowerBasis_dim (a : ℕ) (u : ℤ_[ell]ˣ) :
    (normalizedPowerBasis ell p a u).dim = p := by
  change (fieldPolynomial ell p a u).natDegree = p
  rw [fieldPolynomial,
    (normalizedPolynomial_monic ell p a u (Fact.out : p.Prime).ne_zero).natDegree_map,
    normalizedPolynomial_natDegree]

lemma pi_aeval (a : ℕ) (u : ℤ_[ell]ˣ) :
    aeval (pi ell p a u) (normalizedPolynomial ell p a u) = 0 := by
  have h : aeval (pi ell p a u) (fieldPolynomial ell p a u) = 0 := by
    change aeval (AdjoinRoot.root _) _ = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simpa only [fieldPolynomial, aeval_map_algebraMap] using h

lemma pi_power (a : ℕ) (u : ℤ_[ell]ˣ) :
    (pi ell p a u) ^ p = (ell : NormalizedField ell p a u) *
      (algebraMap ℤ_[ell] (NormalizedField ell p a u) (u : ℤ_[ell])) ^ a := by
  apply sub_eq_zero.mp
  simpa only [normalizedPolynomial, map_sub, map_pow, aeval_X, aeval_C,
    map_mul, map_natCast] using pi_aeval ell p a u

lemma pi_isIntegral (a : ℕ) (u : ℤ_[ell]ˣ) :
    IsIntegral ℤ_[ell] (pi ell p a u) :=
  ⟨normalizedPolynomial ell p a u,
    normalizedPolynomial_monic ell p a u (Fact.out : p.Prime).ne_zero,
    pi_aeval ell p a u⟩

/-- The inverse coefficient is already in Z_ell, since it is a unit inverse. -/
def localRoot (a : ℕ) (u : ℤ_[ell]ˣ) (r b : ℕ) : NormalizedField ell p a u :=
  (pi ell p a u) ^ r *
    algebraMap ℤ_[ell] (NormalizedField ell p a u) ((↑(u⁻¹) : ℤ_[ell]) ^ b)

lemma localRoot_isIntegral (a : ℕ) (u : ℤ_[ell]ˣ) (r b : ℕ) :
    IsIntegral ℤ_[ell] (localRoot ell p a u r b) :=
  ((pi_isIntegral ell p a u).pow r).mul isIntegral_algebraMap

lemma localRoot_power (a : ℕ) (u : ℤ_[ell]ˣ) (r b : ℕ)
    (hab : a * r = b * p + 1) :
    (localRoot ell p a u r b) ^ p = (ell : NormalizedField ell p a u) ^ r *
      algebraMap ℤ_[ell] (NormalizedField ell p a u) (u : ℤ_[ell]) := by
  have hv : algebraMap ℤ_[ell] (NormalizedField ell p a u) (u : ℤ_[ell]) ≠ 0 :=
    (u.isUnit.map (algebraMap ℤ_[ell] (NormalizedField ell p a u))).ne_zero
  simpa only [localRoot, map_pow, map_units_inv] using
    normalized_power_identity p r a b (ell : NormalizedField ell p a u)
      (pi ell p a u)
      (algebraMap ℤ_[ell] (NormalizedField ell p a u) (u : ℤ_[ell]))
      hv (pi_power ell p a u) hab

lemma localRoot_recovery (a : ℕ) (u : ℤ_[ell]ˣ) (r b : ℕ)
    (hab : a * r = b * p + 1) :
    (localRoot ell p a u r b) ^ a =
      (ell : NormalizedField ell p a u) ^ b * pi ell p a u := by
  have hv : algebraMap ℤ_[ell] (NormalizedField ell p a u) (u : ℤ_[ell]) ≠ 0 :=
    (u.isUnit.map (algebraMap ℤ_[ell] (NormalizedField ell p a u))).ne_zero
  simpa only [localRoot, map_pow, map_units_inv] using
    normalized_recovery_identity p r a b (ell : NormalizedField ell p a u)
      (pi ell p a u)
      (algebraMap ℤ_[ell] (NormalizedField ell p a u) (u : ℤ_[ell]))
      hv (pi_power ell p a u) hab

lemma localRoot_power_int (a : ℕ) (u : ℤ_[ell]ˣ) (r b : ℕ)
    (hab : a * r = b * p + 1) (k U : ℤ)
    (hu : (u : ℤ_[ell]) = (U : ℤ_[ell])) (hk : k = (ell : ℤ) ^ r * U) :
    (localRoot ell p a u r b) ^ p = (k : NormalizedField ell p a u) := by
  rw [localRoot_power ell p a u r b hab, hu, map_intCast]
  have h := congrArg (fun z : ℤ => (z : NormalizedField ell p a u)) hk
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using h.symm

/-- The recovery equation proves Q_ell[t] = E; it is not assumed. -/
lemma localRoot_adjoin_eq_top (a : ℕ) (u : ℤ_[ell]ˣ) (r b : ℕ)
    (hab : a * r = b * p + 1) :
    adjoin ℚ_[ell] ({localRoot ell p a u r b} : Set (NormalizedField ell p a u)) = ⊤ := by
  apply PowerBasis.adjoin_eq_top_of_gen_mem_adjoin
    (B := normalizedPowerBasis ell p a u)
  rw [normalizedPowerBasis_gen]
  have hEll : (ell : NormalizedField ell p a u) ≠ 0 := by
    intro h
    apply (Nat.cast_ne_zero.mpr (Fact.out : ell.Prime).ne_zero : (ell : ℚ_[ell]) ≠ 0)
    apply (algebraMap ℚ_[ell] (NormalizedField ell p a u)).injective
    simpa only [map_natCast, map_zero] using h
  have hrecover : pi ell p a u =
      algebraMap ℚ_[ell] (NormalizedField ell p a u) (((ell : ℚ_[ell]) ^ b)⁻¹) *
        (localRoot ell p a u r b) ^ a := by
    rw [localRoot_recovery ell p a u r b hab, map_inv₀, map_pow, map_natCast]
    simp [hEll]
  rw [hrecover]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ _) _)

/-- Actual degree p for t, derived by comparing two power bases in the same field. -/
lemma localRoot_minpoly_natDegree (a : ℕ) (u : ℤ_[ell]ˣ) (r b : ℕ)
    (hab : a * r = b * p + 1) :
    (minpoly ℚ_[ell] (localRoot ell p a u r b)).natDegree = p := by
  have htInt : IsIntegral ℚ_[ell] (localRoot ell p a u r b) :=
    (localRoot_isIntegral ell p a u r b).tower_top
  let e : AdjoinRoot (minpoly ℚ_[ell] (localRoot ell p a u r b)) ≃ₐ[ℚ_[ell]]
      NormalizedField ell p a u :=
    (minpoly.equivAdjoin htInt).trans
      ((Subalgebra.equivOfEq _ _ (localRoot_adjoin_eq_top ell p a u r b hab)).trans
        Subalgebra.topEquiv)
  let T : PowerBasis ℚ_[ell] (NormalizedField ell p a u) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero htInt)).map e
  calc
    (minpoly ℚ_[ell] (localRoot ell p a u r b)).natDegree = T.dim := rfl
    _ = Module.finrank ℚ_[ell] (NormalizedField ell p a u) := T.finrank.symm
    _ = (normalizedPowerBasis ell p a u).dim := (normalizedPowerBasis ell p a u).finrank
    _ = p := normalizedPowerBasis_dim ell p a u

/-- The pure binomial is the minimal polynomial of the actual normalized root. -/
lemma localRoot_binomial_eq_minpoly (a : ℕ) (u : ℤ_[ell]ˣ) (r b : ℕ)
    (hab : a * r = b * p + 1) (k U : ℤ)
    (hu : (u : ℤ_[ell]) = (U : ℤ_[ell])) (hk : k = (ell : ℤ) ^ r * U) :
    (X : ℚ_[ell][X]) ^ p - C (k : ℚ_[ell]) =
      minpoly ℚ_[ell] (localRoot ell p a u r b) := by
  have htInt : IsIntegral ℚ_[ell] (localRoot ell p a u r b) :=
    (localRoot_isIntegral ell p a u r b).tower_top
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic htInt)
    (monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero)
  · apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, map_intCast,
      localRoot_power_int ell p a u r b hab k U hu hk, sub_self]
  · rw [natDegree_X_pow_sub_C, localRoot_minpoly_natDegree ell p a u r b hab]

/-- Concrete construction endpoint. The inputs are just the prime/factorization data.
The unit, exponents, root, integrality, generation, and degree are all constructed. -/
theorem actual_normalized_field (r : ℕ) (hr0 : 0 < r) (hrp : r < p)
    (k U : ℤ) (hk : k = (ell : ℤ) ^ r * U) (hU : ¬ (ell : ℤ) ∣ U) :
    ∃ u : ℤ_[ell]ˣ, (u : ℤ_[ell]) = (U : ℤ_[ell]) ∧
      ∃ a b : ℕ, a < p ∧ a * r = b * p + 1 ∧
        (localRoot ell p a u r b) ^ p = (k : NormalizedField ell p a u) ∧
        (localRoot ell p a u r b) ^ a =
          (ell : NormalizedField ell p a u) ^ b * pi ell p a u ∧
        IsIntegral ℤ_[ell] (localRoot ell p a u r b) ∧
        adjoin ℚ_[ell] ({localRoot ell p a u r b} :
          Set (NormalizedField ell p a u)) = ⊤ ∧
        (minpoly ℚ_[ell] (localRoot ell p a u r b)).natDegree = p := by
  obtain ⟨a, b, ha, hab⟩ :=
    exists_normalizing_exponents p r Fact.out hr0 hrp
  let u : ℤ_[ell]ˣ := integerUnit ell U hU
  have hu : (u : ℤ_[ell]) = (U : ℤ_[ell]) := integerUnit_val ell U hU
  exact ⟨u, hu, a, b, ha, hab,
    localRoot_power_int ell p a u r b hab k U hu hk,
    localRoot_recovery ell p a u r b hab,
    localRoot_isIntegral ell p a u r b,
    localRoot_adjoin_eq_top ell p a u r b hab,
    localRoot_minpoly_natDegree ell p a u r b hab⟩

/-! ## Faithful comparison of the finite integral quotient with the actual field -/

local instance normalizedField_torsionFree (a : ℕ) (u : ℤ_[ell]ˣ) :
    Module.IsTorsionFree ℤ_[ell] (NormalizedField ell p a u) := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  rw [IsScalarTower.algebraMap_eq ℤ_[ell] ℚ_[ell] (NormalizedField ell p a u)]
  exact (algebraMap ℚ_[ell] (NormalizedField ell p a u)).injective.comp
    (IsFractionRing.injective ℤ_[ell] ℚ_[ell])

lemma normalizedPolynomial_eq_ring_minpoly (a : ℕ) (u : ℤ_[ell]ˣ) :
    normalizedPolynomial ell p a u = minpoly ℤ_[ell] (pi ell p a u) :=
  PillaiEisenstein.monic_irreducible_eq_minpoly (K := ℚ_[ell]) _
    (normalizedPolynomial_monic ell p a u (Fact.out : p.Prime).ne_zero)
    (normalizedPolynomial_irreducible ell p a u (Fact.out : p.Prime).ne_zero)
    (pi ell p a u) (pi_aeval ell p a u)

/-- Derived order equivalence, not an assumed embedding or maximality bridge. -/
def normalizedOrderEquiv (a : ℕ) (u : ℤ_[ell]ˣ) :
    AdjoinRoot (normalizedPolynomial ell p a u) ≃ₐ[ℤ_[ell]]
      adjoin ℤ_[ell] ({pi ell p a u} : Set (NormalizedField ell p a u)) :=
  (AdjoinRoot.algEquivOfEq ℤ_[ell] _ _
    (normalizedPolynomial_eq_ring_minpoly ell p a u)).trans
      (minpoly.equivAdjoin (pi_isIntegral ell p a u))

lemma normalizedOrderEquiv_root (a : ℕ) (u : ℤ_[ell]ˣ) :
    ((normalizedOrderEquiv ell p a u)
      (AdjoinRoot.root (normalizedPolynomial ell p a u)) : NormalizedField ell p a u) =
        pi ell p a u := by
  simp only [normalizedOrderEquiv, AlgEquiv.trans_apply, AdjoinRoot.algEquivOfEq_root,
    minpoly.coe_equivAdjoin]
  exact AdjoinRoot.Minpoly.coe_toAdjoin_mk_X (R := ℤ_[ell]) (x := pi ell p a u)

/-- The finite integral quotient maps injectively to the constructed field. -/
def normalizedOrderMap (a : ℕ) (u : ℤ_[ell]ˣ) :
    AdjoinRoot (normalizedPolynomial ell p a u) →ₐ[ℤ_[ell]] NormalizedField ell p a u :=
  (Subalgebra.val _).comp (normalizedOrderEquiv ell p a u).toAlgHom

lemma normalizedOrderMap_injective (a : ℕ) (u : ℤ_[ell]ˣ) :
    Function.Injective (normalizedOrderMap ell p a u) :=
  Subtype.val_injective.comp (normalizedOrderEquiv ell p a u).injective

lemma normalizedOrderMap_root (a : ℕ) (u : ℤ_[ell]ˣ) :
    normalizedOrderMap ell p a u (AdjoinRoot.root (normalizedPolynomial ell p a u)) =
      pi ell p a u :=
  normalizedOrderEquiv_root ell p a u

lemma normalizedOrderMap_aeval (a : ℕ) (u : ℤ_[ell]ˣ) (H : ℤ_[ell][X]) :
    normalizedOrderMap ell p a u
      (aeval (AdjoinRoot.root (normalizedPolynomial ell p a u)) H) =
        aeval (pi ell p a u) H := by
  rw [← aeval_algHom_apply, normalizedOrderMap_root]

/-- The scalar-first generator used by the finite-order lemmas maps to t. -/
lemma normalizedOrderMap_localRoot (a : ℕ) (u : ℤ_[ell]ˣ) (r b : ℕ) :
    normalizedOrderMap ell p a u
      (algebraMap ℤ_[ell] (AdjoinRoot (normalizedPolynomial ell p a u))
        ((↑(u⁻¹) : ℤ_[ell]) ^ b) *
          (AdjoinRoot.root (normalizedPolynomial ell p a u)) ^ r) =
      localRoot ell p a u r b := by
  simp only [map_mul, map_pow, AlgHom.commutes, normalizedOrderMap_root, localRoot]
  exact mul_comm _ _

/-- Maximality is a consequence of the actual Eisenstein data and the previously
checked closure theorem. This theorem is not needed to define E or its map. -/
lemma normalized_integralClosure (a : ℕ) (u : ℤ_[ell]ˣ) :
    integralClosure ℤ_[ell] (NormalizedField ell p a u) =
      adjoin ℤ_[ell] ({pi ell p a u} : Set (NormalizedField ell p a u)) := by
  apply PillaiEisenstein.integralClosure_eq_adjoin_of_polynomial
    (normalizedPowerBasis ell p a u) (ell : ℤ_[ell]) PadicInt.irreducible_p
    (normalizedPolynomial ell p a u)
    (normalizedPolynomial_monic ell p a u (Fact.out : p.Prime).ne_zero)
  · rw [normalizedPolynomial_natDegree]
    exact (Fact.out : p.Prime).pos
  · exact normalizedPolynomial_eisenstein ell p a u (Fact.out : p.Prime).ne_zero
  · exact pi_aeval ell p a u

end PillaiParameterField
