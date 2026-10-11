/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in APACHE-2.0.txt.
Authors: Guanghao Li
Reviewed adaptation from riemann-roch-function-fields commit
 dbca5beed1da77e2ecd1eec207d0451fa57e8aa6.
Changes: isolated local imports and existing reviewed divisor interface;
no external repository imports, build scripts, or metaprograms.
-/
import FractionalDivisorDegree
import SeparableIdealNorm
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-!
# Coordinate places of a function field

This file gives the coordinate presentation of the places of a finite separable extension of
`k(X)`. Finite places are the height-one primes of the integral closure of `k[X]`; infinite
places are the height-one primes of the integral closure of the valuation subring at infinity.

## Main definitions

* `FunctionField.inftyValuationSubring`: the valuation subring at infinity of `k(X)`.
* `FunctionField.infiniteIntegers`: its integral closure in a function field `K`.
* `FunctionField.PlaceA`: the sum of the finite and infinite height-one spectra.
* `FunctionField.placeValuation`: the valuation of a coordinate place.
* `FunctionField.DivisorA`: divisors in the coordinate presentation.
* `FunctionField.principalDivisorA`: the principal divisor on both coordinate charts.
-/



open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace FractionalIdeal

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The multiplicative adic valuation of a nonzero element is the exponential of the negative
coefficient of its principal fractional ideal. -/
theorem valuation_eq_exp_neg_count (v : IsDedekindDomain.HeightOneSpectrum R) (x : Kˣ) :
    v.valuation K (x : K) =
      WithZero.exp (-count K v (spanSingleton R⁰ (x : K))) := by
  let n : R := Classical.choose (IsLocalization.exists_mk'_eq R⁰ (x : K))
  let d : R⁰ := Classical.choose
    (Classical.choose_spec (IsLocalization.exists_mk'_eq R⁰ (x : K)))
  have hx : IsLocalization.mk' K n d = (x : K) :=
    Classical.choose_spec
      (Classical.choose_spec (IsLocalization.exists_mk'_eq R⁰ (x : K)))
  have hn : n ≠ 0 := by
    intro hn
    rw [hn, IsLocalization.mk'_zero] at hx
    exact x.ne_zero hx.symm
  have hI : spanSingleton R⁰ (x : K) =
      spanSingleton R⁰ (algebraMap R K (d : R))⁻¹ *
        (Ideal.span {n} : Ideal R) := by
    rw [← hx, IsFractionRing.mk'_eq_div, div_eq_mul_inv,
      coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, mul_comm]
  conv_lhs =>
    rw [← hx, v.valuation_of_mk', v.intValuation_if_neg hn,
      v.intValuation_if_neg (nonZeroDivisors.ne_zero d.property)]
  rw [count_well_defined K v (spanSingleton_ne_zero_iff.mpr x.ne_zero) hI,
    ← WithZero.exp_sub]
  congr 1
  ring

end FractionalIdeal

namespace RatFunc

variable {k : Type*} [Field k]

/-- A rational function regular at infinity has a unique constant residue: after subtracting
the ratio of the leading coefficients of its numerator and denominator, its degree at infinity
is strictly negative (unless the difference is zero). -/
theorem exists_sub_C_intDegree_neg (z : k⟮X⟯) (hzdeg : z.intDegree ≤ 0) :
    ∃ c : k, z - C c = 0 ∨ (z - C c).intDegree < 0 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  by_cases hneg : z.intDegree < 0
  · exact ⟨0, Or.inr (by simpa using hneg)⟩
  have hzdeg0 : z.intDegree = 0 := by omega
  let c : k := z.num.leadingCoeff / z.denom.leadingCoeff
  let p : k[X] := z.num - Polynomial.C c * z.denom
  have hrepr : z - C c =
      algebraMap k[X] k⟮X⟯ p / algebraMap k[X] k⟮X⟯ z.denom := by
    conv_lhs => lhs; rw [← z.num_div_denom]
    rw [← RatFunc.algebraMap_C]
    simp only [p, map_sub, map_mul]
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero z.denom_ne_zero)).2
    rw [sub_mul, div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero z.denom_ne_zero)]
  by_cases hp : p = 0
  · exact ⟨c, Or.inl (by rw [hrepr, hp, map_zero, zero_div])⟩
  refine ⟨c, Or.inr ?_⟩
  have hnumdeg : z.num.natDegree = z.denom.natDegree := by
    simp only [RatFunc.intDegree] at hzdeg0
    omega
  have hnum0 : z.num ≠ 0 := RatFunc.num_ne_zero hz
  have hden0 : z.denom ≠ 0 := z.denom_ne_zero
  have hlcnum : z.num.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hnum0
  have hlcden : z.denom.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hden0
  have hc : c ≠ 0 := div_ne_zero hlcnum hlcden
  have hCmul0 : Polynomial.C c * z.denom ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hden0
  have hdegree : z.num.degree = (Polynomial.C c * z.denom).degree := by
    rw [Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_mul,
      Polynomial.degree_C hc, zero_add, Polynomial.degree_eq_natDegree hden0, hnumdeg]
  have hlc : z.num.leadingCoeff =
      (Polynomial.C c * z.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    dsimp only [c]
    field_simp
  have hpdeg : p.degree < z.num.degree := by
    simpa only [p] using Polynomial.degree_sub_lt hdegree hnum0 hlc
  have hpnat : p.natDegree < z.denom.natDegree := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hp]
    rw [← hnumdeg]
    simpa [Polynomial.degree_eq_natDegree hnum0] using hpdeg
  rw [hrepr, RatFunc.intDegree_div]
  · simp only [RatFunc.intDegree_polynomial]
    omega
  · exact RatFunc.algebraMap_ne_zero hp
  · exact RatFunc.algebraMap_ne_zero hden0

end RatFunc

namespace FunctionField
variable (k K : Type*) [Field k] [Field K]
namespace Chart

/-- The classical decidable equality used to define the valuation at infinity. -/
local instance instDecidableEqRatFuncRiemannRoch : DecidableEq k⟮X⟯ := Classical.decEq _

/-- The valuation subring at infinity of the rational function field `k(X)`. -/
abbrev inftyValuationSubring := (RatFunc.inftyValuation k).valuationSubring

namespace inftyValuationSubring

instance : IsDedekindDomain (inftyValuationSubring k) := by infer_instance

instance : Algebra k (inftyValuationSubring k) :=
  (RatFunc.C.codRestrict (inftyValuationSubring k) fun c => by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (RatFunc.inftyValuation.C k hc).le).toAlgebra

local notation "ᵐ∞" => IsLocalRing.maximalIdeal (inftyValuationSubring k)

/-- The residue field at infinity. -/
local instance : Field (inftyValuationSubring k ⧸ ᵐ∞) := Ideal.Quotient.field ᵐ∞

/-- The residue map at infinity is onto the constant field. -/
theorem residue_algebraMap_surjective :
    Function.Surjective (algebraMap k (inftyValuationSubring k ⧸ ᵐ∞)) := by
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  let z : k⟮X⟯ := (a : k⟮X⟯)
  have hzdeg : z.intDegree ≤ 0 := by
    by_cases hz : z = 0
    · simp [hz]
    have ha := a.property
    rw [Valuation.mem_valuationSubring_iff] at ha
    change RatFunc.inftyValuation k z ≤ 1 at ha
    have hv : RatFunc.inftyValuation k z = WithZero.exp z.intDegree :=
      RatFunc.inftyValuation_of_nonzero k hz
    rw [hv] at ha
    exact WithZero.exp_le_exp.mp (by simpa only [WithZero.exp_zero] using ha)
  obtain ⟨c, hc | hc⟩ := RatFunc.exists_sub_C_intDegree_neg z hzdeg
  · refine ⟨c, ?_⟩
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have hzero : algebraMap k (inftyValuationSubring k) c - a = 0 := by
      apply Subtype.ext
      change RatFunc.C c - z = 0
      rw [show RatFunc.C c - z = -(z - RatFunc.C c) by ring, hc, neg_zero]
    rw [hzero]
    exact ᵐ∞.zero_mem
  · refine ⟨c, ?_⟩
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have hne : z - RatFunc.C c ≠ 0 := by
      intro h
      rw [h, RatFunc.intDegree_zero] at hc
      omega
    have hpos : a - algebraMap k (inftyValuationSubring k) c ∈ ᵐ∞ := by
      rw [Valuation.mem_maximalIdeal_iff]
      change RatFunc.inftyValuation k (z - RatFunc.C c) < 1
      have hv : RatFunc.inftyValuation k (z - RatFunc.C c) =
          WithZero.exp (z - RatFunc.C c).intDegree :=
        RatFunc.inftyValuation_of_nonzero k hne
      rw [hv]
      exact WithZero.exp_lt_exp.mpr hc
    simpa only [neg_sub] using ᵐ∞.neg_mem hpos

/-- The residue field of the valuation ring at infinity is canonically the constant field. -/
noncomputable def residueAlgEquiv :
    k ≃ₐ[k] (inftyValuationSubring k ⧸ ᵐ∞) :=
  AlgEquiv.ofBijective (Algebra.ofId k (inftyValuationSubring k ⧸ ᵐ∞))
    ⟨(Algebra.ofId k (inftyValuationSubring k ⧸ ᵐ∞)).injective,
      residue_algebraMap_surjective k⟩

instance finiteDimensionalResidueField :
    FiniteDimensional k (inftyValuationSubring k ⧸ ᵐ∞) :=
  (residueAlgEquiv k).toLinearEquiv.finiteDimensional

@[simp]
theorem finrank_residueField :
    Module.finrank k (inftyValuationSubring k ⧸ ᵐ∞) = 1 := by
  rw [← (residueAlgEquiv k).toLinearEquiv.finrank_eq]
  exact Module.finrank_self k

end inftyValuationSubring

variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

/-- The integral closure in `K` of the valuation subring at infinity of `k(X)`. -/
abbrev infiniteIntegers := integralClosure (inftyValuationSubring k) K

namespace infiniteIntegers

instance isTorsionFreeOverInfinityRing :
    Module.IsTorsionFree (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsIntegralClosure.isTorsionFree (inftyValuationSubring k) K

instance : IsFractionRing (infiniteIntegers k K) K :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (inftyValuationSubring k) k⟮X⟯ K (infiniteIntegers k K)

instance : IsDedekindDomain (infiniteIntegers k K) :=
  integralClosure.isDedekindDomain (inftyValuationSubring k) k⟮X⟯ K

instance : Module.Finite (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsIntegralClosure.finite (inftyValuationSubring k) k⟮X⟯ K (infiniteIntegers k K)

instance : Algebra k (infiniteIntegers k K) :=
  ((algebraMap (inftyValuationSubring k) (infiniteIntegers k K)).comp
    (algebraMap k (inftyValuationSubring k))).toAlgebra

instance : IsScalarTower k (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := inftyValuationSubring k)
    (A := infiniteIntegers k K) fun _ => rfl

end infiniteIntegers

namespace ringOfIntegers

instance isTorsionFreeOverPolynomial :
    Module.IsTorsionFree k[X] (ringOfIntegers k K) := by
  letI : FaithfulSMul k[X] K :=
    (faithfulSMul_iff_algebraMap_injective k[X] K).2
      (FunctionField.algebraMap_injective k K)
  exact IsIntegralClosure.isTorsionFree k[X] K

instance algebraOverConstants : Algebra k (ringOfIntegers k K) :=
  ((algebraMap k[X] (ringOfIntegers k K)).comp (algebraMap k k[X])).toAlgebra

instance isScalarTowerConstants : IsScalarTower k k[X] (ringOfIntegers k K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance finiteTypeOverConstants : Algebra.FiniteType k (ringOfIntegers k K) :=
  Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance

instance moduleFiniteOverPolynomial : Module.Finite k[X] (ringOfIntegers k K) :=
  IsIntegralClosure.finite k[X] k⟮X⟯ K (ringOfIntegers k K)

end ringOfIntegers

/-- Coordinate places of `K`: finite places on the `k[X]` chart and places above infinity. -/
abbrev PlaceA :=
  IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K) ⊕
    IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)

/-- The discrete valuation associated to a coordinate place. -/
def placeValuation : PlaceA k K → Valuation K ℤᵐ⁰
  | Sum.inl v => v.valuation K
  | Sum.inr v => v.valuation K

/-- Divisors on `K` in the two-chart coordinate presentation. -/
abbrev DivisorA := PlaceA k K →₀ ℤ

namespace PlaceA

/-- The residue field at a finite coordinate place is finite-dimensional over the constant
field. -/
instance finiteDimensionalResidueFieldFinite
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    FiniteDimensional k (ringOfIntegers k K ⧸ v.asIdeal) := by
  letI : Field (ringOfIntegers k K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  exact finite_of_finite_type_of_isJacobsonRing k _

/-- The residue field at an infinite coordinate place is finite-dimensional over the constant
field. -/
instance finiteDimensionalResidueFieldInfinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    FiniteDimensional k (infiniteIntegers k K ⧸ v.asIdeal) := by
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let p : Ideal A := v.asIdeal.under A
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : p.IsMaximal := Ideal.IsMaximal.under A v.asIdeal
  letI : v.asIdeal.LiesOver p := ⟨rfl⟩
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Algebra (A ⧸ p) (S ⧸ v.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def v.asIdeal p).ge
  have hp : p = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
  letI : FiniteDimensional k (A ⧸ p) := by
    rw [hp]
    exact inftyValuationSubring.finiteDimensionalResidueField k
  letI : FiniteDimensional (A ⧸ p) (S ⧸ v.asIdeal) := by
    have hfin := Ideal.inertiaDeg'_pos p v.asIdeal
    rw [Ideal.inertiaDeg'_algebraMap] at hfin
    exact FiniteDimensional.of_finrank_pos hfin
  letI : IsScalarTower k (A ⧸ p) (S ⧸ v.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact FiniteDimensional.trans k (A ⧸ p) (S ⧸ v.asIdeal)

/-- The degree of a finite coordinate place over the constant field. -/
noncomputable def finiteDegree
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) : ℕ :=
  Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal)

end PlaceA

/-- The principal divisor of a nonzero function, combining its finite and infinite parts. -/
noncomputable def principalDivisorA : Additive Kˣ →+ DivisorA k K :=
  (Finsupp.mapDomain.addMonoidHom Sum.inl).comp
      (Astra01.DedekindDivisor.principalDivisor (R := ringOfIntegers k K) (K := K)) +
    (Finsupp.mapDomain.addMonoidHom Sum.inr).comp
      (Astra01.DedekindDivisor.principalDivisor (R := infiniteIntegers k K) (K := K))

@[simp]
theorem principalDivisorA_apply_finite (x : Additive Kˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    principalDivisorA k K x (Sum.inl v) =
      Astra01.DedekindDivisor.principalDivisor (R := ringOfIntegers k K) (K := K) x v := by
  simp only [principalDivisorA, AddMonoidHom.add_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  change Finsupp.mapDomain Sum.inl
      (Astra01.DedekindDivisor.principalDivisor (R := ringOfIntegers k K) (K := K) x) (Sum.inl v) +
    Finsupp.mapDomain Sum.inr
      (Astra01.DedekindDivisor.principalDivisor (R := infiniteIntegers k K) (K := K) x)
        (Sum.inl v) = _
  rw [Finsupp.mapDomain_apply Sum.inl_injective]
  rw [Finsupp.mapDomain_notin_range]
  · simp
  · rintro ⟨w, h⟩
    cases h

@[simp]
theorem principalDivisorA_apply_infinite (x : Additive Kˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    principalDivisorA k K x (Sum.inr v) =
      Astra01.DedekindDivisor.principalDivisor (R := infiniteIntegers k K) (K := K) x v := by
  simp only [principalDivisorA, AddMonoidHom.add_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  change Finsupp.mapDomain Sum.inl
      (Astra01.DedekindDivisor.principalDivisor (R := ringOfIntegers k K) (K := K) x) (Sum.inr v) +
    Finsupp.mapDomain Sum.inr
      (Astra01.DedekindDivisor.principalDivisor (R := infiniteIntegers k K) (K := K) x)
        (Sum.inr v) = _
  rw [Finsupp.mapDomain_apply Sum.inr_injective]
  rw [Finsupp.mapDomain_notin_range]
  · simp
  · rintro ⟨w, h⟩
    cases h

/-- A principal-divisor coefficient is the negative logarithm of the corresponding valuation. -/
theorem placeValuation_eq_exp_neg_principalDivisor (x : Additive Kˣ) (v : PlaceA k K) :
    placeValuation k K v (x.toMul : K) =
      WithZero.exp (-(principalDivisorA k K x v)) := by
  rcases v with v | v
  · rw [principalDivisorA_apply_finite, Astra01.DedekindDivisor.principalDivisor_apply]
    exact FractionalIdeal.valuation_eq_exp_neg_count v x.toMul
  · rw [principalDivisorA_apply_infinite, Astra01.DedekindDivisor.principalDivisor_apply]
    exact FractionalIdeal.valuation_eq_exp_neg_count v x.toMul

section ConstantField

variable [Algebra k K] [IsScalarTower k k[X] K]

instance ringOfIntegers.isScalarTowerConstantsFractions :
    IsScalarTower k (ringOfIntegers k K) K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k[X] (ringOfIntegers k K) K,
      ← IsScalarTower.algebraMap_apply k k[X] (ringOfIntegers k K)]

instance infiniteIntegers.isScalarTowerConstantsFractions :
    IsScalarTower k (infiniteIntegers k K) K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    have h₁ : algebraMap k (infiniteIntegers k K) c =
        algebraMap (inftyValuationSubring k) (infiniteIntegers k K)
          (algebraMap k (inftyValuationSubring k) c) := rfl
    have h₂ : algebraMap (inftyValuationSubring k) k⟮X⟯
        (algebraMap k (inftyValuationSubring k) c) = RatFunc.C c := rfl
    rw [h₁, ← IsScalarTower.algebraMap_apply (inftyValuationSubring k) (infiniteIntegers k K) K,
      IsScalarTower.algebraMap_apply (inftyValuationSubring k) k⟮X⟯ K, h₂,
      IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K, Polynomial.algebraMap_eq,
      RatFunc.algebraMap_C]

/-- Constants have valuation at most one at every coordinate place. -/
theorem placeValuation_algebraMap_le_one (v : PlaceA k K) (c : k) :
    placeValuation k K v (algebraMap k K c) ≤ 1 := by
  obtain w | w := v
  · show w.valuation K (algebraMap k K c) ≤ 1
    rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) K]
    exact w.valuation_le_one _
  · show w.valuation K (algebraMap k K c) ≤ 1
    rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K) K]
    exact w.valuation_le_one _

/-- A nonzero constant has trivial valuation at every coordinate place. -/
theorem placeValuation_algebraMap_eq_one (v : PlaceA k K) (c : kˣ) :
    placeValuation k K v (algebraMap k K (c : k)) = 1 := by
  have hc_le := placeValuation_algebraMap_le_one k K v (c : k)
  have hc_inv_le := placeValuation_algebraMap_le_one k K v ((c⁻¹ : kˣ) : k)
  have hmap_ne : placeValuation k K v (algebraMap k K (c : k)) ≠ 0 := by
    rw [map_ne_zero]
    exact (map_ne_zero (algebraMap k K)).2 c.ne_zero
  have hmap_pos : 0 < placeValuation k K v (algebraMap k K (c : k)) :=
    WithZero.pos_iff_ne_zero.2 hmap_ne
  have hinv_le : (placeValuation k K v (algebraMap k K (c : k)))⁻¹ ≤ 1 := by
    simpa using hc_inv_le
  exact le_antisymm hc_le ((inv_le_one₀ hmap_pos).1 hinv_le)

/-- Multiplying by a nonzero constant does not change a principal divisor. -/
@[simp]
theorem principalDivisorA_algebraMap (c : kˣ) :
    principalDivisorA k K
        (Additive.ofMul (Units.map (algebraMap k K) c)) = 0 := by
  ext v
  simp only [Finsupp.zero_apply]
  have hv := placeValuation_eq_exp_neg_principalDivisor k K
    (Additive.ofMul (Units.map (algebraMap k K) c)) v
  change placeValuation k K v (algebraMap k K (c : k)) = _ at hv
  rw [placeValuation_algebraMap_eq_one k K v c] at hv
  have hexp : WithZero.exp (0 : ℤ) =
      WithZero.exp
        (-(principalDivisorA k K
          (Additive.ofMul (Units.map (algebraMap k K) c)) v)) := by
    simpa using hv
  exact neg_eq_zero.mp (WithZero.exp_injective hexp.symm)

end ConstantField

end Chart

end FunctionField

#print axioms FunctionField.Chart.placeValuation_eq_exp_neg_principalDivisor
#print axioms FunctionField.Chart.inftyValuationSubring.finrank_residueField
