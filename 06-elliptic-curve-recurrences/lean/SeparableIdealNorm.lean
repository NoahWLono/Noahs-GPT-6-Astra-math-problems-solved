/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in APACHE-2.0.txt.
Authors: Guanghao Li
Reviewed adaptation from riemann-roch-function-fields commit
 dbca5beed1da77e2ecd1eec207d0451fa57e8aa6.
Changes: isolated local imports and existing reviewed divisor interface;
no external repository imports, build scripts, or metaprograms.
-/
import SeparablePrimeNorm
open Module UniqueFactorizationMonoid
open scoped nonZeroDivisors
namespace Ideal
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [IsTorsionFree R S]
/-- Relative norm preserves the weighted sum of prime factors, with each prime upstairs weighted
by its inertia degree over the prime below. -/
theorem sum_normalizedFactors_relNorm_of_isSeparable
    [@Algebra.IsSeparable (FractionRing R) (FractionRing S) _ _
      (FractionRing.liftAlgebra R (FractionRing S))]
    (I : Ideal S) (hI : I ≠ ⊥) (w : Ideal R → ℕ) :
    ((normalizedFactors (relNorm R I)).map w).sum =
      ((normalizedFactors I).map fun P =>
        (P.under R).inertiaDeg' P * w (P.under R)).sum := by
  classical
  letI : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  have aux : ∀ s : Multiset (Ideal S), (∀ P ∈ s, Prime P) →
      ((normalizedFactors (relNorm R s.prod)).map w).sum =
        (s.map fun P => (P.under R).inertiaDeg' P * w (P.under R)).sum := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty =>
        rw [Multiset.prod_zero, map_one]
        simp only [normalizedFactors_one, Multiset.map_zero, Multiset.sum_zero]
    | @cons P s ih =>
        have hP : Prime P := hs P (Multiset.mem_cons_self P s)
        have hs' : ∀ Q ∈ s, Prime Q := fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
        have hP0 : P ≠ ⊥ := hP.ne_zero
        have hs0 : s.prod ≠ ⊥ := Multiset.prod_ne_zero fun h =>
          (hs' ⊥ h).ne_zero rfl
        let p : Ideal R := P.under R
        letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP0
        letI : p.IsMaximal := Ideal.IsMaximal.under R P
        letI : P.LiesOver p := ⟨rfl⟩
        have hp0 : p ≠ ⊥ := by
          intro hp
          haveI : P.LiesOver (⊥ : Ideal R) := hp ▸ (inferInstance : P.LiesOver p)
          exact hP0 (Ideal.eq_bot_of_liesOver_bot R P)
        have hnorm : relNorm R P = p ^ (P.under R).inertiaDeg' P :=
          by simpa only [inertiaDeg'_eq_inertiaDeg] using
            relNorm_eq_pow_of_isMaximal_of_isSeparable P p
        have hnormP0 : relNorm R P ≠ ⊥ := (relNorm_eq_bot_iff.not.mpr hP0)
        have hnorms0 : relNorm R s.prod ≠ ⊥ :=
          relNorm_eq_bot_iff.not.mpr hs0
        rw [Multiset.prod_cons, map_mul, normalizedFactors_mul hnormP0 hnorms0,
          Multiset.map_add, Multiset.sum_add, hnorm, normalizedFactors_pow,
          UniqueFactorizationMonoid.normalizedFactors_irreducible
            (Ideal.prime_of_isPrime hp0
              (inferInstance : p.IsMaximal).isPrime).irreducible,
          normalize_eq, Multiset.nsmul_singleton]
        simp [ih hs', p]
  let s := normalizedFactors I
  have hsprod : s.prod = I := prod_normalizedFactors_eq_self hI
  calc
    ((normalizedFactors (relNorm R I)).map w).sum =
        ((normalizedFactors (relNorm R s.prod)).map w).sum := by rw [hsprod]
    _ = (s.map fun P => (P.under R).inertiaDeg' P * w (P.under R)).sum := by
      apply aux s
      intro P hP
      exact UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    _ = ((normalizedFactors I).map fun P =>
        (P.under R).inertiaDeg' P * w (P.under R)).sum := rfl

end Ideal

#print axioms Ideal.relNorm_eq_pow_of_isMaximal_of_isSeparable
#print axioms Ideal.sum_normalizedFactors_relNorm_of_isSeparable
