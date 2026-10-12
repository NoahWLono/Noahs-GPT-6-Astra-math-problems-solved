import EisensteinIntegralClosure
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-! A supplied monic Eisenstein equation implies the actual integral-closure equality. -/
set_option autoImplicit false
open Algebra Polynomial
namespace PillaiEisenstein
universe u v w
variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [IsDomain R] [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

include K in
/-- Identify the ring-minimal polynomial from the supplied monic irreducible equation. -/
theorem monic_irreducible_eq_minpoly [IsIntegrallyClosed R]
    (f : R[X]) (hf : f.Monic) (hirr : Irreducible f) (z : L) (hz : aeval z f=0) :
    f=minpoly R z := by
  have hi : IsIntegral R z := ⟨f,hf,hz⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K hi]
  apply minpoly.eq_of_irreducible_of_monic
  · exact hf.irreducible_iff_irreducible_map_fraction_map.mp hirr
  · rw [aeval_map_algebraMap,hz]
  · exact hf.map _

/-- A monic Eisenstein defining equation, rather than an assumed minimal-polynomial identity,
proves maximality of the actual DVR power order. -/
theorem integralClosure_eq_adjoin_of_polynomial [IsDiscreteValuationRing R]
    (B : PowerBasis K L) (π : R) (hπ : Irreducible π)
    (f : R[X]) (hf : f.Monic) (hdeg : 0<f.natDegree)
    (he : f.IsEisensteinAt (Ideal.span {π})) (hroot : aeval B.gen f=0) :
    integralClosure R L=adjoin R ({B.gen} : Set L) := by
  have hprime : (Ideal.span {π}).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ.prime
  have hirr := he.irreducible hprime hf.isPrimitive hdeg
  have hmin := monic_irreducible_eq_minpoly (K := K) f hf hirr B.gen hroot
  apply integralClosure_eq_adjoin B π hπ ⟨f,hf,hroot⟩
  rwa [← hmin]

end PillaiEisenstein
