/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in APACHE-2.0.txt.
Authors: Guanghao Li
Reviewed adaptation from riemann-roch-function-fields commit
 dbca5beed1da77e2ecd1eec207d0451fa57e8aa6.
Changes: isolated local imports and existing reviewed divisor interface;
no external repository imports, build scripts, or metaprograms.
-/
import DedekindDivisor
namespace Astra01.DedekindDivisor
open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
omit [IsDedekindDomain R] in
@[simp]
theorem weightedDegree_apply (w : Ideal R → ℕ) (D : Divisor R) :
    weightedDegree (R := R) w D =
      D.sum fun v n => n * (w v.asIdeal : ℤ) := rfl

/-- The weighted degree of the divisor of a nonzero integral ideal is the weighted sum of its
normalized prime factors.  The weight is stated on ideals, so that it can later be chosen as a
residue-field degree or an inertia-weighted residue-field degree. -/
theorem divisor_ideal_sum_eq_normalizedFactors_sum (J : Ideal R) (hJ : J ≠ ⊥)
    (w : Ideal R → ℕ) :
    let JU : (FractionalIdeal R⁰ K)ˣ :=
      Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ)
    (divisor JU).sum (fun v n => n * (w v.asIdeal : ℤ)) =
      (((UniqueFactorizationMonoid.normalizedFactors J).map w).sum : ℤ) := by
  classical
  dsimp only
  rw [Finsupp.sum]
  let s := UniqueFactorizationMonoid.normalizedFactors J
  have hcoeff (v : HeightOneSpectrum R) :
      divisor (Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ)) v =
        (s.count v.asIdeal : ℤ) := by
    rw [divisor_apply, Units.val_mk0, count_coe K v hJ,
      Ideal.count_associates_factors_eq hJ v.isPrime v.ne_bot]
  have hsum :
      ∑ v ∈ (divisor
          (Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ))).support,
          divisor (Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ)) v *
            (w v.asIdeal : ℤ) =
        ∑ P ∈ s.toFinset, (s.count P : ℤ) * (w P : ℤ) := by
    apply Finset.sum_bij (fun v _ => v.asIdeal)
    · intro v hv
      rw [Multiset.mem_toFinset, ← Multiset.count_ne_zero]
      intro hz
      have : divisor
          (Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ)) v = 0 := by
        rw [hcoeff, hz, Nat.cast_zero]
      exact (Finsupp.mem_support_iff.mp hv) this
    · intro v₁ _ v₂ _ hv
      exact HeightOneSpectrum.ext hv
    · intro P hP
      rw [Multiset.mem_toFinset] at hP
      have hprime : Prime P :=
        UniqueFactorizationMonoid.prime_of_normalized_factor P hP
      let v : HeightOneSpectrum R :=
        ⟨P, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩
      refine ⟨v, ?_, rfl⟩
      rw [Finsupp.mem_support_iff, hcoeff]
      exact_mod_cast (Multiset.count_pos.mpr hP).ne'
    · intro v _
      rw [hcoeff]
  rw [hsum, Finset.sum_multiset_map_count]
  simp only [s, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul]
  push_cast
  rfl

/-- Weighted degree of the divisor of a nonzero integral ideal. -/
theorem weightedDegree_divisor_ideal (J : Ideal R) (hJ : J ≠ ⊥)
    (w : Ideal R → ℕ) :
    weightedDegree (R := R) w
        (divisor (Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ))) =
      (((UniqueFactorizationMonoid.normalizedFactors J).map w).sum : ℤ) :=
  divisor_ideal_sum_eq_normalizedFactors_sum J hJ w

/-- If a nonzero fraction is represented by `n / d`, its weighted principal-divisor degree is
the weighted factor degree of `n` minus that of `d`. -/
theorem weightedDegree_principal_mk' (w : Ideal R → ℕ) (x : Kˣ) (n : R)
    (d : nonZeroDivisors R) (hnd : IsLocalization.mk' K n d = (x : K)) :
    weightedDegree (R := R) w (principalDivisor (Additive.ofMul x)) =
      (((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).map w).sum : ℤ) -
        (((UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span {(d : R)})).map w).sum : ℤ) := by
  classical
  have hn : n ≠ 0 := by
    intro hn
    exact x.ne_zero (by simpa [hn] using hnd.symm)
  have hd : (d : R) ≠ 0 := by
    simpa only [mem_nonZeroDivisors_iff_ne_zero] using d.property
  have hspan : spanSingleton R⁰ (x : K) =
      spanSingleton R⁰ ((algebraMap R K) (d : R))⁻¹ *
        (Ideal.span {n} : FractionalIdeal R⁰ K) := by
    rw [← hnd, IsFractionRing.mk'_eq_div, coeIdeal_span_singleton,
      spanSingleton_mul_spanSingleton]
    congr 1
    simp only [div_eq_mul_inv]
    ac_rfl
  have hdiv : principalDivisor (R := R) (K := K) (Additive.ofMul x) =
      divisor (Units.mk0 (Ideal.span {n} : FractionalIdeal R⁰ K)
          (coeIdeal_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hn))) -
        divisor (Units.mk0 (Ideal.span {(d : R)} : FractionalIdeal R⁰ K)
          (coeIdeal_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hd))) := by
    ext v
    rw [principalDivisor_apply, Finsupp.sub_apply, divisor_apply, divisor_apply]
    change count K v (spanSingleton R⁰ (x : K)) =
      count K v (Ideal.span {n} : FractionalIdeal R⁰ K) -
        count K v (Ideal.span {(d : R)} : FractionalIdeal R⁰ K)
    rw [count_well_defined K v (spanSingleton_ne_zero_iff.mpr x.ne_zero) hspan,
      count_coe K v (Ideal.span_singleton_eq_bot.not.mpr hn),
      count_coe K v (Ideal.span_singleton_eq_bot.not.mpr hd)]
  rw [hdiv, map_sub,
    weightedDegree_divisor_ideal (K := K) (Ideal.span {n})
      (Ideal.span_singleton_eq_bot.not.mpr hn) w,
    weightedDegree_divisor_ideal (K := K) (Ideal.span {(d : R)})
      (Ideal.span_singleton_eq_bot.not.mpr hd) w]


#print axioms weightedDegree_principal_mk'
end Astra01.DedekindDivisor
