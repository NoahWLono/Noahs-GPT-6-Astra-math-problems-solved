import AlgebraicPowerPropagation
import ReducedEisensteinCoordinates
import IntegralTranslateLift
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Tower

/-!
# B nonsplit branch: actual translated-Eisenstein coefficient lift

Elaborated with pinned Lean 4.32.2 and mathlib commit
905b95818eb32af7874a58b427f50c1711a5e96c. The exact clean build, axioms audit,
and checking limitations are recorded beside this source.
No assumptions about local integrality, a local integral basis, field embeddings,
or coordinate integrality are introduced.
-/

set_option autoImplicit false

open Algebra Polynomial

namespace PillaiLocalCoefficients

universe u

/-- The actual translated Eisenstein alternative gives a reduced integral lift
of the rational polynomial in the affine power equation. The root extension,
power basis, minimal polynomial and local integrality are all constructed here. -/
theorem padic_polynomial_lift_of_translated_eisenstein
    (p q : ℕ) [Fact p.Prime] (hq : 0 < q)
    (k A : ℤ)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ)
    (he : (((X : ℤ_[p][X]) + C (k : ℤ_[p])) ^ p - C (k : ℤ_[p])).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])})) :
    ∃ P : ℤ_[p][X], P.natDegree < p ∧
      P.map (algebraMap ℤ_[p] ℚ_[p]) = G.map (algebraMap ℚ ℚ_[p]) := by
  have hp : p.Prime := Fact.out
  let f : ℤ_[p][X] := (X + C (k : ℤ_[p])) ^ p - C (k : ℤ_[p])
  have hf : f.Monic := by
    apply ((monic_X_add_C _).pow p).sub_of_left
    apply degree_C_le.trans_lt
    rw [degree_eq_natDegree ((monic_X_add_C _).pow p).ne_zero,
      natDegree_pow_X_add_C]
    exact WithBot.coe_lt_coe.mpr hp.pos
  have hfdeg : f.natDegree = p := by
    simp only [f, natDegree_sub_C, natDegree_pow_X_add_C]
  have hfpos : 0 < f.natDegree := by
    rw [hfdeg]
    exact hp.pos
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have hirrf : Irreducible f := he.irreducible hprime hf.isPrimitive hfpos
  let F : ℚ_[p][X] := f.map (algebraMap ℤ_[p] ℚ_[p])
  have hirrF : Irreducible F :=
    hf.irreducible_iff_irreducible_map_fraction_map.mp hirrf
  letI : Fact (Irreducible F) := ⟨hirrF⟩
  let B : PowerBasis ℚ_[p] (AdjoinRoot F) := AdjoinRoot.powerBasis hirrF.ne_zero
  have hrootF : aeval B.gen F = 0 := by
    change aeval (AdjoinRoot.root F) F = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hroot : aeval B.gen f = 0 := by
    have hh : aeval B.gen (f.map (algebraMap ℤ_[p] ℚ_[p])) = 0 := hrootF
    simpa only [aeval_map_algebraMap] using hh
  have hmin : F = minpoly ℚ_[p] B.gen := by
    apply minpoly.eq_of_irreducible_of_monic hirrF hrootF
    exact hf.map _
  have hgenInt : IsIntegral ℤ_[p] B.gen := ⟨f, hf, hroot⟩
  let t : AdjoinRoot F := B.gen + (k : AdjoinRoot F)
  have ht : t ^ p = (k : AdjoinRoot F) := by
    apply sub_eq_zero.mp
    simpa only [f, t, map_sub, map_pow, map_add, aeval_X, aeval_C, map_intCast]
      using hroot
  have hkInt : IsIntegral ℤ_[p] (k : AdjoinRoot F) := by
    simpa only [map_intCast] using
      (isIntegral_algebraMap : IsIntegral ℤ_[p]
        (algebraMap ℤ_[p] (AdjoinRoot F) (k : ℤ_[p])))
  have htInt : IsIntegral ℤ_[p] t := hgenInt.add hkInt
  have hGInt : IsIntegral ℤ_[p] (aeval t G) :=
    propagated_aeval_isIntegral p q hq k A θ hθ hirr G heq t ht htInt
  let GK : ℚ_[p][X] := G.map (algebraMap ℚ ℚ_[p])
  let Gshift : ℚ_[p][X] := GK.comp (X + C (k : ℚ_[p]))
  have hGKdeg : GK.natDegree < p := lt_of_le_of_lt natDegree_map_le hG
  have hGshiftdeg : Gshift.natDegree < f.natDegree := by
    dsimp only [Gshift]
    rw [natDegree_comp, natDegree_X_add_C, mul_one, hfdeg]
    exact hGKdeg
  have hGshiftEval : aeval B.gen Gshift = aeval t G := by
    dsimp only [Gshift]
    rw [aeval_comp]
    simp only [map_add, aeval_X, map_intCast]
    change aeval t (G.map (algebraMap ℚ ℚ_[p])) = aeval t G
    exact aeval_map_algebraMap ℚ_[p] t G
  have hGshiftInt : IsIntegral ℤ_[p] (aeval B.gen Gshift) := by
    rw [hGshiftEval]
    exact hGInt
  obtain ⟨H, hHdeg, hH⟩ := reduced_polynomial_lift_of_isIntegral
    B (p : ℤ_[p]) PadicInt.irreducible_p f hf hfpos he hroot
    Gshift hGshiftdeg hGshiftInt
  apply integral_lift_of_integral_translate p (k : ℤ_[p]) GK H
  · simpa only [hfdeg] using hHdeg
  · simpa only [Gshift, map_intCast] using hH

end PillaiLocalCoefficients
