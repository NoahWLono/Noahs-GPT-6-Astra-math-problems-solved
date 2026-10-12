import MonicEisensteinClosure
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Reduced Eisenstein coordinates

Elaborated with Lean 4.32.2 at mathlib pin
905b95818eb32af7874a58b427f50c1711a5e96c. See the adjacent verification records
for source hashes, exact endpoints, resource guards, and checking limitations.
This source is outside every sealed handoff.

The integral-closure equality comes from the already compiled
PillaiEisenstein.integralClosure_eq_adjoin_of_polynomial. The representative is
constructed from adjoin membership and reduced by monic division. Its uniqueness
is deduced from the actual field minimal polynomial, which is derived here from
the supplied Eisenstein polynomial and root equation.
-/

set_option autoImplicit false

open Algebra Polynomial

namespace PillaiLocalCoefficients

universe u v w

variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [IsDomain R] [Field K] [Field L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- a reduced polynomial evaluating to an integral element has an
actual reduced representative over the DVR. No coefficient-integrality,
maximal-order, degree-identification, or minpoly-identification bridge is assumed. -/
theorem reduced_polynomial_lift_of_isIntegral [IsDiscreteValuationRing R]
    (B : PowerBasis K L) (π : R) (hπ : Irreducible π)
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (he : f.IsEisensteinAt (Ideal.span {π}))
    (hroot : aeval B.gen f = 0)
    (G : K[X]) (hG : G.natDegree < f.natDegree)
    (hInt : IsIntegral R (aeval B.gen G)) :
    ∃ H : R[X], H.natDegree < f.natDegree ∧ H.map (algebraMap R K) = G := by
  have hprime : (Ideal.span {π}).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ.prime
  have hirr : Irreducible f := he.irreducible hprime hf.isPrimitive hdeg
  have hmin : f.map (algebraMap R K) = minpoly K B.gen := by
    apply minpoly.eq_of_irreducible_of_monic
    · exact hf.irreducible_iff_irreducible_map_fraction_map.mp hirr
    · rw [aeval_map_algebraMap, hroot]
    · exact hf.map _
  have hminDeg : (minpoly K B.gen).natDegree = f.natDegree := by
    rw [← hmin]
    exact hf.natDegree_map _

  have hclosure : integralClosure R L = adjoin R ({B.gen} : Set L) :=
    PillaiEisenstein.integralClosure_eq_adjoin_of_polynomial
      B π hπ f hf hdeg he hroot
  have hmem : aeval B.gen G ∈ adjoin R ({B.gen} : Set L) := by
    rw [← hclosure]
    exact hInt
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨Q, hQ⟩ := hmem

  let H : R[X] := Q %ₘ f
  have hfOne : f ≠ 1 := by
    intro h
    simp only [h, natDegree_one, lt_self_iff_false] at hdeg
  have hH : H.natDegree < f.natDegree :=
    natDegree_modByMonic_lt Q hf hfOne
  have hHeval : aeval B.gen H = aeval B.gen G := by
    change aeval B.gen (Q %ₘ f) = aeval B.gen G
    rw [aeval_modByMonic_eq_self_of_root hroot]
    exact hQ
  have hzero : aeval B.gen (H.map (algebraMap R K) - G) = 0 := by
    rw [map_sub, aeval_map_algebraMap, hHeval, sub_self]
  have hdvd : minpoly K B.gen ∣ H.map (algebraMap R K) - G :=
    minpoly.dvd K B.gen hzero
  have hmapDeg : (H.map (algebraMap R K)).natDegree < f.natDegree :=
    lt_of_le_of_lt natDegree_map_le hH
  have hdiffDeg : (H.map (algebraMap R K) - G).natDegree <
      (minpoly K B.gen).natDegree := by
    rw [hminDeg]
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hmapDeg hG)
  refine ⟨H, hH, ?_⟩
  exact sub_eq_zero.mp (eq_zero_of_dvd_of_natDegree_lt hdvd hdiffDeg)

/-- the corresponding literal coefficient-image conclusion. -/
theorem coefficients_mem_base_of_isIntegral [IsDiscreteValuationRing R]
    (B : PowerBasis K L) (π : R) (hπ : Irreducible π)
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (he : f.IsEisensteinAt (Ideal.span {π}))
    (hroot : aeval B.gen f = 0)
    (G : K[X]) (hG : G.natDegree < f.natDegree)
    (hInt : IsIntegral R (aeval B.gen G)) :
    ∀ j : ℕ, ∃ a : R, algebraMap R K a = G.coeff j := by
  obtain ⟨H, _, hH⟩ := reduced_polynomial_lift_of_isIntegral
    B π hπ f hf hdeg he hroot G hG hInt
  intro j
  refine ⟨H.coeff j, ?_⟩
  have hc := congrArg (fun P : K[X] => P.coeff j) hH
  simpa only [coeff_map] using hc

end PillaiLocalCoefficients
