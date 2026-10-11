/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in APACHE-2.0.txt.
Authors: Guanghao Li

Reviewed and adapted from RiemannRoch/Divisor.lean at
https://github.com/vaca22/riemann-roch-function-fields/tree/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6
Changes: isolated Astra01 namespace, restricted interface, pinned Mathlib 4.32.2,
explicit axiom audits. No external repository imports or metaprograms.
-/
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! Genuine Dedekind-domain divisors, built from Mathlib fractional-ideal
factorizations. These are affine divisors. No assertion that their degree
is zero for principal divisors is made: the missing infinity contribution
is essential in the intended projective-curve application. -/
namespace Astra01.DedekindDivisor
open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

abbrev Divisor (R : Type*) [CommRing R] := HeightOneSpectrum R →₀ ℤ
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

noncomputable def divisor (I : (FractionalIdeal R⁰ K)ˣ) : Divisor R :=
  Finsupp.mk (finite_factors (I : FractionalIdeal R⁰ K)).toFinset
    (fun v ↦ count K v I) fun _ ↦ (finite_factors (I : FractionalIdeal R⁰ K)).mem_toFinset

@[simp] theorem divisor_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    divisor I v = count K v I := by
  classical
  simp [divisor]

noncomputable def ofDivisor (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (D : Divisor R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (D.prod fun v n ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ n) <| by
    classical
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
      zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] theorem count_ofDivisor (D : Divisor R) (v : HeightOneSpectrum R) :
    count K v (ofDivisor K D : FractionalIdeal R⁰ K) = D v := by
  classical
  simpa [ofDivisor] using count_finsuppProd K v D

private theorem eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v, count K v I = count K v J) : I = J := by
  rw [← finprod_heightOneSpectrum_factorization' K hI,
    ← finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v ↦ congr_arg ((v.asIdeal : FractionalIdeal R⁰ K) ^ ·) (h v)

/-- Multiplicative fractional ideals identify with additive divisors. -/
noncomputable def divisorEquiv : Additive (FractionalIdeal R⁰ K)ˣ ≃+ Divisor R where
  toFun I := divisor I.toMul
  invFun D := Additive.ofMul (ofDivisor K D)
  left_inv I := by
    apply Additive.toMul.injective
    apply Units.ext
    change (ofDivisor K (divisor I.toMul) : FractionalIdeal R⁰ K) = I.toMul
    apply eq_of_count_eq (ofDivisor K (divisor I.toMul)).ne_zero I.toMul.ne_zero
    intro v
    rw [count_ofDivisor, divisor_apply]
  right_inv D := by
    ext v
    change count K v (ofDivisor K D : FractionalIdeal R⁰ K) = D v
    rw [count_ofDivisor]
  map_add' I J := by
    change divisor (I.toMul * J.toMul) = divisor I.toMul + divisor J.toMul
    ext v
    simp only [divisor_apply, Units.val_mul]
    exact count_mul K v I.toMul.ne_zero J.toMul.ne_zero

noncomputable def principalIdeal : Kˣ →* (FractionalIdeal R⁰ K)ˣ where
  toFun x := Units.mk0 (spanSingleton R⁰ (x : K)) (spanSingleton_ne_zero_iff.mpr x.ne_zero)
  map_one' := Units.ext spanSingleton_one
  map_mul' x y := Units.ext (spanSingleton_mul_spanSingleton (R := R) (x : K) y).symm

noncomputable def principalDivisor : Additive Kˣ →+ Divisor R :=
  divisorEquiv.toAddMonoidHom.comp principalIdeal.toAdditive

@[simp] theorem principalDivisor_apply (x : Additive Kˣ) (v : HeightOneSpectrum R) :
    principalDivisor (R := R) (K := K) x v =
      count K v (spanSingleton R⁰ (x.toMul : K)) := by
  change divisor (principalIdeal x.toMul) v = _
  rw [divisor_apply]
  rfl

/-- Residue-field degrees can subsequently supply the weights. -/
noncomputable def weightedDegree (w : Ideal R → ℕ) : Divisor R →+ ℤ where
  toFun D := D.sum fun v n => n * (w v.asIdeal : ℤ)
  map_zero' := by simp
  map_add' D E := by
    classical
    simp [Finsupp.sum_add_index, add_mul]

#print axioms divisorEquiv
#print axioms principalDivisor_apply
#print axioms weightedDegree
end Astra01.DedekindDivisor
