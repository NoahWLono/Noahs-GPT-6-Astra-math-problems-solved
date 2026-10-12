import AlgebraicPowerPropagation
import ActualPadicSplit
import Mathlib.RingTheory.Polynomial.Tower

/-!
# The actual split branch of the p-local coefficient lift

Elaborated with pinned Lean 4.32.2 and mathlib commit
905b95818eb32af7874a58b427f50c1711a5e96c. The exact clean build, axioms audit,
and checking limitations are recorded beside this source.

The only branch-specific hypothesis is an actual unit p-th root in Z_p.
Integrality of both evaluations and the scalar integral lift are derived.
-/

set_option autoImplicit false

open Polynomial

namespace PillaiLocalCoefficients

/-- If the binomial has an actual unit root in Z_p, the rational polynomial in
the affine prime-power relation has an integral polynomial lift of degree < p. -/
theorem split_integral_polynomial_lift
    (p q : ℕ) [Fact p.Prime] (hq : q.Prime) (hpq : p < q)
    (k A : ℤ)
    {L : Type*} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ)
    (b : ℤ_[p]) (hb : b ^ p = (k : ℤ_[p])) (hbUnit : IsUnit b) :
    ∃ P : ℤ_[p][X], P.natDegree < p ∧
      P.map (algebraMap ℤ_[p] ℚ_[p]) = G.map (algebraMap ℚ ℚ_[p]) := by
  obtain ⟨bUnit, rfl⟩ := hbUnit
  let s : ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] (bUnit : ℤ_[p])
  let t : PillaiCyclotomic.LocalField p :=
    algebraMap ℤ_[p] (PillaiCyclotomic.LocalField p) (bUnit : ℤ_[p]) *
      PillaiCyclotomic.zeta p
  have hs : s ^ p = (k : ℚ_[p]) := by
    simpa only [s, map_pow, map_intCast] using
      congrArg (algebraMap ℤ_[p] ℚ_[p]) hb
  have hbField :
      (algebraMap ℤ_[p] (PillaiCyclotomic.LocalField p) (bUnit : ℤ_[p])) ^ p =
        (k : PillaiCyclotomic.LocalField p) := by
    simpa only [map_pow, map_intCast] using
      congrArg (algebraMap ℤ_[p] (PillaiCyclotomic.LocalField p)) hb
  have ht : t ^ p = (k : PillaiCyclotomic.LocalField p) := by
    dsimp only [t]
    rw [mul_pow, hbField, (PillaiCyclotomic.zeta_primitive p).pow_eq_one, mul_one]
  have hsInt : IsIntegral ℤ_[p] s := isIntegral_algebraMap
  have htInt : IsIntegral ℤ_[p] t := by
    exact (isIntegral_algebraMap (x := (bUnit : ℤ_[p]))).mul
      (PillaiCyclotomic.cyclotomic_root_integral p (PillaiCyclotomic.zeta p)
        (PillaiCyclotomic.zeta_aeval p))
  have hsEquation : (aeval s G) ^ q = (A : ℚ_[p]) - s :=
    power_equation_at_root p q k A θ hθ hirr G heq s hs
  have htEquation :
      (aeval t G) ^ q = (A : PillaiCyclotomic.LocalField p) - t :=
    power_equation_at_root p q k A θ hθ hirr G heq t ht
  have hsGInt : IsIntegral ℤ_[p] (aeval s G) :=
    isIntegral_of_integer_power_equation q hq.pos A (aeval s G) s hsInt hsEquation
  have htGInt : IsIntegral ℤ_[p] (aeval t G) :=
    isIntegral_of_integer_power_equation q hq.pos A (aeval t G) t htInt htEquation
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hsGInt
  have hxEquation : x ^ q = (A : ℤ_[p]) - (bUnit : ℤ_[p]) := by
    apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    simpa only [map_pow, map_sub, map_intCast, hx, s] using hsEquation
  have hyEquation :
      (aeval t G) ^ q =
        algebraMap ℤ_[p] (PillaiCyclotomic.LocalField p) (A : ℤ_[p]) -
          algebraMap ℤ_[p] (PillaiCyclotomic.LocalField p) (bUnit : ℤ_[p]) *
            PillaiCyclotomic.zeta p := by
    simpa only [map_intCast, t] using htEquation
  obtain ⟨P, hP, hPx, hPy⟩ :=
    PillaiCyclotomic.actual_split_power_equation p q hq hpq bUnit (A : ℤ_[p]) x
      (aeval t G) htGInt hxEquation hyEquation
  refine ⟨P, hP, ?_⟩
  let bField : ℚ_[p]ˣ := Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom bUnit
  apply PillaiCyclotomic.actual_split_evaluation_unique p bField
    (P.map (algebraMap ℤ_[p] ℚ_[p])) (G.map (algebraMap ℚ ℚ_[p]))
    (lt_of_le_of_lt natDegree_map_le hP) (lt_of_le_of_lt natDegree_map_le hG)
  · change (P.map (algebraMap ℤ_[p] ℚ_[p])).eval
        (algebraMap ℤ_[p] ℚ_[p] (bUnit : ℤ_[p])) =
      (G.map (algebraMap ℚ ℚ_[p])).eval
        (algebraMap ℤ_[p] ℚ_[p] (bUnit : ℤ_[p]))
    rw [eval_map_apply, eval_map_algebraMap, hPx]
    exact hx
  · have hroot :
        algebraMap ℚ_[p] (PillaiCyclotomic.LocalField p) (bField : ℚ_[p]) *
          PillaiCyclotomic.zeta p = t := by
      change algebraMap ℚ_[p] (PillaiCyclotomic.LocalField p)
          (algebraMap ℤ_[p] ℚ_[p] (bUnit : ℤ_[p])) * PillaiCyclotomic.zeta p =
        algebraMap ℤ_[p] (PillaiCyclotomic.LocalField p) (bUnit : ℤ_[p]) *
          PillaiCyclotomic.zeta p
      rw [← IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p]
        (PillaiCyclotomic.LocalField p)]
    rw [hroot]
    simpa only [aeval_map_algebraMap] using hPy

end PillaiLocalCoefficients
