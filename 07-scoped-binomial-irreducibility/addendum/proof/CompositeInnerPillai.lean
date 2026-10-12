import ScopedPillaiIrreducibility
import Mathlib.FieldTheory.KummerExtension

/-!
# Composite inner exponents with all prime factors larger than the outer prime

This is an immediate corollary of the checked scoped affine exclusion. No new
coefficient-integrality or affine-exclusion assumptions are introduced.
-/

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace PillaiScoped

/-- The inner exponent need not be prime: it suffices that all its prime
divisors are larger than the outer prime. -/
theorem irreducible_composition_of_inner_prime_factors_gt
    (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 < m)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ m → p < q)
    (k A : ℤ) (hk : 1 < |k|)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p) :
    Irreducible (((X : ℚ[X]) ^ m - C (A : ℚ)) ^ p + C (k : ℚ)) := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hm)
  have hnot2 : ¬ 2 ∣ m := by
    intro h2
    exact (not_lt_of_ge (le_trans (by decide : 2 ≤ 5) hp5))
      (hprime 2 Nat.prime_two h2)
  have hmodd : Odd m := Nat.not_even_iff_odd.mp fun heven =>
    hnot2 (even_iff_two_dvd.mp heven)
  have hpodd : Odd p :=
    hp.odd_of_ne_two (ne_of_gt (lt_of_lt_of_le (by decide : 2 < 5) hp5))
  have hkabs : 1 < k.natAbs := by
    apply Int.ofNat_lt.mp
    simpa only [Int.natCast_natAbs, Nat.cast_one] using hk
  have hirr := PillaiGlobalCoefficients.rational_binomial_irreducible_of_valuation_bounds
    p hp k hkabs hval
  have houter := PillaiCapelliBridge.outer_irreducible p hp hpodd k hirr
  have hcomp : Irreducible
      (((X : ℚ[X]) ^ p + C (k : ℚ)).comp
        ((X : ℚ[X]) ^ m - C (A : ℚ))) := by
    apply Polynomial.irreducible_comp
      (monic_X_pow_add_C (k : ℚ) hp.ne_zero)
      (monic_X_pow_sub_C (A : ℚ) hm0) houter
    intro L _ _ α hmin
    -- Keep the root field's inherited rational algebra, as in the checked
    -- representatives, rather than the general division-ring rational algebra.
    letI : Algebra ℚ ℚ⟮α⟯ := (ℚ⟮α⟯).algebra'
    have hθ : (-AdjoinSimple.gen ℚ α) ^ p = (k : ℚ⟮α⟯) :=
      PillaiCapelliBridge.neg_generator_power p hpodd k α hmin
    have hnopow : ∀ q : ℕ, q.Prime → q ∣ m → ∀ β : ℚ⟮α⟯,
        β ^ q ≠ (A : ℚ⟮α⟯) - (-AdjoinSimple.gen ℚ α) := by
      intro q hq hqm β hβ
      obtain ⟨G, hG, hrepr⟩ :=
        PillaiCapelliBridge.exists_reduced_neg_generator_representation
          p hp.ne_zero k α hmin β
      apply reduced_affine_power_equation_exclusion
        p q hp hq hp5 (hprime q hq hqm) k A hk hval
        (-AdjoinSimple.gen ℚ α) hθ G hG
      exact (congrArg (fun z : ℚ⟮α⟯ => z ^ q) hrepr).symm.trans hβ
    have hbin : Irreducible ((X : ℚ⟮α⟯[X]) ^ m -
        C ((A : ℚ⟮α⟯) - (-AdjoinSimple.gen ℚ α))) :=
      X_pow_sub_C_irreducible_of_odd hmodd hnopow
    have hpoly :
        (((X : ℚ[X]) ^ m - C (A : ℚ)).map (algebraMap ℚ ℚ⟮α⟯) -
          C (AdjoinSimple.gen ℚ α)) =
        (X : ℚ⟮α⟯[X]) ^ m - C ((A : ℚ⟮α⟯) - (-AdjoinSimple.gen ℚ α)) := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_intCast, map_intCast, sub_neg_eq_add, map_add, sub_sub]
    exact (congrArg Irreducible hpoly).mpr hbin
  simpa only [PillaiCapelliBridge.composition_identity p m k A] using hcomp

end PillaiScoped
