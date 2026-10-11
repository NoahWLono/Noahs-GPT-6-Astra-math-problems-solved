/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in APACHE-2.0.txt.
Authors: Guanghao Li
Reviewed adaptation of the finite-affine portion of
RiemannRoch/EllipticCurve/PlaceDictionary.lean at commit
 dbca5beed1da77e2ecd1eec207d0451fa57e8aa6.
Changes: no external imports or function-field tower; direct Mathlib
coordinate-ring primes, residue degree, and an explicit surjectivity endpoint.
-/
import EllipticAffineDivisor
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring

namespace Astra01.EllipticPlaces
open WeierstrassCurve.Affine
noncomputable section
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]

lemma pointIdeal_maximal {x y : k} (h : W.Nonsingular x y) :
    (CoordinateRing.XYIdeal W x (Polynomial.C y)).IsMaximal := by
  let e := CoordinateRing.quotientXYIdealEquiv (W' := W) (x := x)
    (y := Polynomial.C y) h.1
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
    (e.toRingEquiv.isField (Field.toIsField k))

lemma pointIdeal_ne_bot {x y : k} (_h : W.Nonsingular x y) :
    CoordinateRing.XYIdeal W x (Polynomial.C y) ≠ ⊥ := by
  intro hbot
  apply CoordinateRing.XClass_ne_zero (W' := W) x
  rw [← Ideal.mem_bot, ← hbot]
  exact Ideal.subset_span (Set.mem_insert _ _)

/-- A nonsingular affine rational point gives a genuine finite prime. -/
def pointPrime {x y : k} (h : W.Nonsingular x y) :
    IsDedekindDomain.HeightOneSpectrum W.CoordinateRing :=
  ⟨CoordinateRing.XYIdeal W x (Polynomial.C y),
    (pointIdeal_maximal W h).isPrime, pointIdeal_ne_bot W h⟩

/-- Its residue field has degree one over the base field. -/
theorem pointPrime_residue_degree {x y : k} (h : W.Nonsingular x y) :
    Module.finrank k (W.CoordinateRing ⧸ (pointPrime W h).asIdeal) = 1 := by
  let e := CoordinateRing.quotientXYIdealEquiv (W' := W) (x := x)
    (y := Polynomial.C y) h.1
  exact e.toLinearEquiv.finrank_eq.trans (Module.finrank_self k)

lemma maximal_eq_pointIdeal [IsAlgClosed k] (I : Ideal W.CoordinateRing) [I.IsMaximal] :
    ∃ x y : k, ∃ _ : W.Nonsingular x y,
      I = CoordinateRing.XYIdeal W x (Polynomial.C y) := by
  let L := W.CoordinateRing ⧸ I
  letI : Field L := Ideal.Quotient.field I
  haveI : Algebra.FiniteType k L := Algebra.FiniteType.quotient k I
  haveI : Module.Finite k L := finite_of_finite_type_of_isJacobsonRing k L
  haveI : Algebra.IsIntegral k L := Algebra.IsIntegral.of_finite k L
  obtain ⟨x, hx⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
    (Ideal.Quotient.mk I (CoordinateRing.mk W (Polynomial.C Polynomial.X)))
  obtain ⟨y, hy⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
    (Ideal.Quotient.mk I (CoordinateRing.mk W Polynomial.X))
  have heq : W.Equation x y := by
    apply (W.map_equation (algebraMap k L).injective x y).mp
    rw [hx, hy]
    simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map] using
      (coordinate_equation W).map (Ideal.Quotient.mk I)
  have hns : W.Nonsingular x y := W.equation_iff_nonsingular.mp heq
  have hle : CoordinateRing.XYIdeal W x (Polynomial.C y) ≤ I := by
    rw [CoordinateRing.XYIdeal, Ideal.span_le]
    rintro z (rfl | hz)
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [CoordinateRing.XClass, map_sub]
      rw [sub_eq_zero]
      change (Ideal.Quotient.mk I) (CoordinateRing.mk W (Polynomial.C Polynomial.X)) =
        algebraMap k L x
      exact hx.symm
    · have : z = CoordinateRing.YClass W (Polynomial.C y) := by simpa using hz
      subst z
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simp only [CoordinateRing.YClass, map_sub]
      rw [sub_eq_zero]
      change (Ideal.Quotient.mk I) (CoordinateRing.mk W Polynomial.X) =
        algebraMap k L y
      exact hy.symm
  refine ⟨x, y, hns, ?_⟩
  exact ((pointIdeal_maximal W hns).eq_of_le (Ideal.IsMaximal.ne_top inferInstance) hle).symm

/-- Over algebraically closed constants, every finite prime comes from an affine point. -/
theorem every_finite_prime_is_point [IsAlgClosed k]
    (v : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing) :
    ∃ x y : k, ∃ h : W.Nonsingular x y, v = pointPrime W h := by
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  obtain ⟨x,y,h,heq⟩ := maximal_eq_pointIdeal W v.asIdeal
  exact ⟨x,y,h,IsDedekindDomain.HeightOneSpectrum.ext heq⟩

#print axioms pointPrime_residue_degree
#print axioms every_finite_prime_is_point
end
end Astra01.EllipticPlaces
