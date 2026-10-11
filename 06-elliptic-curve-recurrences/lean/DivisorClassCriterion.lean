import DedekindDivisor
import Mathlib.RingTheory.ClassGroup.Basic

/-! A genuine class-group criterion for principal fractional-ideal divisors.
This uses Mathlib's quotient by principal fractional ideals; no principal
criterion is assumed. -/
namespace Astra01.DedekindDivisor
noncomputable section
open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

def divisorClass : Divisor R →+ Additive (ClassGroup R) :=
  (ClassGroup.mk K).toAdditive.comp (divisorEquiv (R := R) (K := K)).symm.toAddMonoidHom

theorem exists_principalIdeal_of_class_one (I : (FractionalIdeal R⁰ K)ˣ)
    (h : ClassGroup.mk K I = 1) : ∃ f : Kˣ, principalIdeal f = I := by
  have hI := ClassGroup.mk_eq_one_iff.mp h
  obtain ⟨x,hx⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hI
  have he : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ x := by
    apply Subtype.coe_injective
    simp only [val_eq_coe, hx, coe_spanSingleton]
  have hx0 : x ≠ 0 := by
    intro hx0
    apply I.ne_zero
    simp [he, hx0]
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Units.ext
  exact he.symm

theorem exists_principalDivisor_of_class_zero (D : Divisor R)
    (h : divisorClass (K := K) D = 0) :
    ∃ f : Kˣ, principalDivisor (R := R) (Additive.ofMul f) = D := by
  change ClassGroup.mk K (ofDivisor K D) = 1 at h
  obtain ⟨f,hf⟩ := exists_principalIdeal_of_class_one (ofDivisor K D) h
  refine ⟨f, ?_⟩
  change divisorEquiv (Additive.ofMul (principalIdeal f)) = D
  rw [hf]
  exact (divisorEquiv (R := R) (K := K)).apply_symm_apply D
end
end Astra01.DedekindDivisor
#print axioms Astra01.DedekindDivisor.exists_principalDivisor_of_class_zero
