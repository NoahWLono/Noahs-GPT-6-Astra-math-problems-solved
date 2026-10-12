import GlobalCoefficientAssembly
import SignedRealExclusion
import CapelliPureFieldBridge

/-!
# Scoped prime-valuation composition irreducibility

All rational irreducibility, integer coefficient, scalar nonvanishing, signed
real-root and Capelli obligations are derived from the displayed arithmetic
hypotheses. The parameter and scalar are arbitrary signed integers.
-/

set_option autoImplicit false
open Polynomial

namespace PillaiScoped

universe u

/-- The valuation bounds exclude every reduced rational affine power equation
in an arbitrary rational-algebra field containing an actual pure root. -/
theorem reduced_affine_power_equation_exclusion
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p) (hpq : p < q)
    (k A : ℤ) (hk : 1 < |k|)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (G : ℚ[X]) (hG : G.natDegree < p) :
    (aeval θ G) ^ q ≠ (A : L) - θ := by
  intro heq
  have hkabs : 1 < k.natAbs := by
    apply Int.ofNat_lt.mp
    simpa only [Int.natCast_natAbs, Nat.cast_one] using hk
  have hirr := PillaiGlobalCoefficients.rational_binomial_irreducible_of_valuation_bounds
    p hp k hkabs hval
  obtain ⟨hA, H, hH, hmap⟩ := PillaiGlobalCoefficients.integer_polynomial_of_power_equation
    p q hp (le_trans (by decide : 3 ≤ 5) hp5) hq hpq k A hkabs hval θ hθ G hG heq
  apply PillaiSignedRealExclusion.signed_mapped_integer_polynomial_affine_exclusion
    p q hp hp5 hq hpq k hk hirr A hA θ hθ H hH
  rw [hmap]
  exact heq

/-- For primes 5 ≤ p < q and a nonunit signed integer parameter whose prime
valuations are all below p, the advertised composition is irreducible over Q.
There is no auxiliary affine-exclusion or coefficient-integrality premise. -/
theorem irreducible_composition_of_prime_valuation_bounds
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p) (hpq : p < q)
    (k A : ℤ) (hk : 1 < |k|)
    (hval : ∀ ell : ℕ, ell.Prime → (ell : ℤ) ∣ k → padicValInt ell k < p) :
    Irreducible (((X : ℚ[X]) ^ q - C (A : ℚ)) ^ p + C (k : ℚ)) := by
  have hkabs : 1 < k.natAbs := by
    apply Int.ofNat_lt.mp
    simpa only [Int.natCast_natAbs, Nat.cast_one] using hk
  have hirr := PillaiGlobalCoefficients.rational_binomial_irreducible_of_valuation_bounds
    p hp k hkabs hval
  apply PillaiCapelliBridge.irreducible_composition_of_reduced_affine_exclusion
    p q hp (hp.odd_of_ne_two (ne_of_gt (lt_of_lt_of_le (by decide : 2 < 5) hp5)))
    hq k A hirr
  intro L _ _ θ hθ G hG
  exact reduced_affine_power_equation_exclusion p q hp hq hp5 hpq k A hk hval θ hθ G hG

end PillaiScoped
