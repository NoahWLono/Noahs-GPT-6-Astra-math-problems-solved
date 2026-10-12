import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Prime.Basic

/-! Checked-stage helper for the scoped arithmetic composition assembly.
The final theorem must discharge every explicit helper premise. -/

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace PillaiCapelliBridge

universe u

/-- The helper dependency to be discharged by D's arithmetic argument.
`Type` suffices for the concrete rational-polynomial Capelli application:
its auxiliary fields and simple subfields are in the universe of `ℚ`.
This is a definition of a proposition, not an additional proof assumption. -/
def ReducedAffineExclusion (p q : ℕ) (k A : ℤ) : Prop :=
  ∀ (L : Type) [Field L] [Algebra ℚ L]
    (θ : L), θ ^ p = (k : L) →
      ∀ (G : ℚ[X]), G.natDegree < p →
        (aeval θ G) ^ q ≠ (A : L) - θ

/-- The sign change in the outer polynomial is literal polynomial equality. -/
theorem outer_sign_identity (p : ℕ) (hpodd : Odd p) (k : ℤ) :
    (((X : ℚ[X]) ^ p + C (k : ℚ)).comp (-X)) =
      -((X : ℚ[X]) ^ p - C (k : ℚ)) := by
  simp only [add_comp, pow_comp, X_comp, C_comp, hpodd.neg_pow,
    sub_eq_add_neg, neg_add, neg_neg]

/-- Prime Kummer irreducibility transfers from `X^p-k` to `X^p+k`
when `p` is odd. -/
theorem outer_irreducible
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) (k : ℤ)
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ))) :
    Irreducible ((X : ℚ[X]) ^ p + C (k : ℚ)) := by
  have hnotpow : ∀ b : ℚ, b ^ p ≠ (k : ℚ) :=
    (X_pow_sub_C_irreducible_iff_of_prime hp).mp hirr
  have hneg : Irreducible ((X : ℚ[X]) ^ p - C (-(k : ℚ))) := by
    apply X_pow_sub_C_irreducible_of_prime hp
    intro b hb
    apply hnotpow (-b)
    rw [hpodd.neg_pow, hb, neg_neg]
  simpa only [map_neg, sub_neg_eq_add] using hneg

/-- The Capelli root really is integral, as its given minimal polynomial
is a nonzero monic polynomial. -/
theorem outer_root_isIntegral
    {L : Type u} [Field L] [Algebra ℚ L]
    (p : ℕ) (hp0 : p ≠ 0) (k : ℤ) (α : L)
    (hmin : minpoly ℚ α = (X : ℚ[X]) ^ p + C (k : ℚ)) :
    IsIntegral ℚ α := by
  apply minpoly.ne_zero_iff.mp
  rw [hmin]
  exact (monic_X_pow_add_C (k : ℚ) hp0).ne_zero

/-- The actual simple extension has degree `p`; no degree assumption. -/
theorem outer_root_finrank
    {L : Type u} [Field L] [Algebra ℚ L]
    (p : ℕ) (hp0 : p ≠ 0) (k : ℤ) (α : L)
    (hmin : minpoly ℚ α = (X : ℚ[X]) ^ p + C (k : ℚ)) :
    Module.finrank ℚ ℚ⟮α⟯ = p := by
  rw [IntermediateField.adjoin.finrank
    (outer_root_isIntegral p hp0 k α hmin), hmin, natDegree_X_pow_add_C]

/-- The internal `θ = -gen(α)` maps to the ambient `-α`. -/
theorem algebraMap_neg_generator
    {L : Type u} [Field L] [Algebra ℚ L] (α : L) :
    algebraMap ℚ⟮α⟯ L (-AdjoinSimple.gen ℚ α) = -α := by
  rw [map_neg, AdjoinSimple.algebraMap_gen]

/-- Evaluation of the actual minimal polynomial gives the sign-correct
pure-binomial equation inside the actual simple extension. -/
theorem neg_generator_power
    {L : Type u} [Field L] [Algebra ℚ L]
    (p : ℕ) (hpodd : Odd p) (k : ℤ) (α : L)
    (hmin : minpoly ℚ α = (X : ℚ[X]) ^ p + C (k : ℚ)) :
    (-AdjoinSimple.gen ℚ α) ^ p = (k : ℚ⟮α⟯) := by
  have hz : aeval (AdjoinSimple.gen ℚ α)
      ((X : ℚ[X]) ^ p + C (k : ℚ)) = 0 := by
    rw [← hmin]
    exact IntermediateField.aeval_gen_minpoly ℚ α
  simp only [map_add, map_pow, aeval_X, map_intCast] at hz
  have hpow : (AdjoinSimple.gen ℚ α) ^ p = -(k : ℚ⟮α⟯) :=
    eq_neg_of_add_eq_zero_left hz
  rw [hpodd.neg_pow, hpow, neg_neg]

/-- The signed generator has exactly the original pure minimal polynomial. -/
theorem neg_generator_minpoly
    {L : Type u} [Field L] [Algebra ℚ L]
    (p : ℕ) (hp0 : p ≠ 0) (hpodd : Odd p) (k : ℤ) (α : L)
    (hmin : minpoly ℚ α = (X : ℚ[X]) ^ p + C (k : ℚ))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ))) :
    minpoly ℚ (-AdjoinSimple.gen ℚ α) = (X : ℚ[X]) ^ p - C (k : ℚ) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic hirr
  · simp only [map_sub, map_pow, aeval_X, map_intCast,
      neg_generator_power p hpodd k α hmin, sub_self]
  · exact monic_X_pow_sub_C (k : ℚ) hp0

/-- Every element of the actual Capelli root field has a reduced rational
polynomial representative in `θ = -gen(α)`. The proof obtains `H` from the
actual power basis, then uses `G = H.comp (-X)`; both the representation
and the strict degree bound are conclusions, not assumptions. -/
theorem exists_reduced_neg_generator_representation
    {L : Type u} [Field L] [Algebra ℚ L]
    (p : ℕ) (hp0 : p ≠ 0) (k : ℤ) (α : L)
    (hmin : minpoly ℚ α = (X : ℚ[X]) ^ p + C (k : ℚ))
    (β : ℚ⟮α⟯) :
    ∃ G : ℚ[X], G.natDegree < p ∧ β = aeval (-AdjoinSimple.gen ℚ α) G := by
  have hα : IsIntegral ℚ α := outer_root_isIntegral p hp0 k α hmin
  obtain ⟨H, hH, hβ⟩ :=
    (IntermediateField.adjoin.powerBasis hα).exists_eq_aeval β
  have hHdeg : H.natDegree < p := by
    simpa only [IntermediateField.adjoin.powerBasis_dim, hmin,
      natDegree_X_pow_add_C] using hH
  refine ⟨H.comp (-X), ?_, ?_⟩
  · simpa only [natDegree_comp, natDegree_neg, natDegree_X, mul_one] using hHdeg
  · rw [aeval_comp]
    simpa only [map_neg, aeval_X, neg_neg,
      IntermediateField.adjoin.powerBasis_gen] using hβ

/-- Literal target/Capelli composition identity. -/
theorem composition_identity (p q : ℕ) (k A : ℤ) :
    (((X : ℚ[X]) ^ p + C (k : ℚ)).comp
      ((X : ℚ[X]) ^ q - C (A : ℚ))) =
      ((X : ℚ[X]) ^ q - C (A : ℚ)) ^ p + C (k : ℚ) := by
  simp only [add_comp, pow_comp, X_comp, C_comp]

/-- The final polynomial really has degree `p*q`. -/
theorem composition_natDegree (p q : ℕ) (k A : ℤ) :
    (((X : ℚ[X]) ^ q - C (A : ℚ)) ^ p + C (k : ℚ)).natDegree = p * q := by
  rw [← composition_identity p q k A, natDegree_comp,
    natDegree_X_pow_add_C, natDegree_X_pow_sub_C]

/-- GENERIC HELPER ONLY. Actual Capelli irreducibility follows from an
already-proved affine exclusion. This declaration does not discharge that
arithmetic dependency and must not be advertised as the final D theorem. -/
theorem irreducible_composition_of_reduced_affine_exclusion
    (p q : ℕ) (hp : p.Prime) (hpodd : Odd p) (hq : q.Prime)
    (k A : ℤ)
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (hexclude : ReducedAffineExclusion p q k A) :
    Irreducible (((X : ℚ[X]) ^ q - C (A : ℚ)) ^ p + C (k : ℚ)) := by
  have houter := outer_irreducible p hp hpodd k hirr
  have hcomp : Irreducible
      (((X : ℚ[X]) ^ p + C (k : ℚ)).comp
        ((X : ℚ[X]) ^ q - C (A : ℚ))) := by
    apply Polynomial.irreducible_comp
      (monic_X_pow_add_C (k : ℚ) hp.ne_zero)
      (monic_X_pow_sub_C (A : ℚ) hq.ne_zero) houter
    intro L _ _ α hmin
    have hθ : (-AdjoinSimple.gen ℚ α) ^ p = (k : ℚ⟮α⟯) :=
      neg_generator_power p hpodd k α hmin
    have hnopow : ∀ β : ℚ⟮α⟯,
        β ^ q ≠ (A : ℚ⟮α⟯) - (-AdjoinSimple.gen ℚ α) := by
      intro β hβ
      obtain ⟨G, hG, hrepr⟩ :=
        exists_reduced_neg_generator_representation p hp.ne_zero k α hmin β
      apply hexclude ℚ⟮α⟯ (-AdjoinSimple.gen ℚ α) hθ G hG
      rw [← hrepr]
      exact hβ
    have hbin : Irreducible ((X : ℚ⟮α⟯[X]) ^ q -
        C ((A : ℚ⟮α⟯) - (-AdjoinSimple.gen ℚ α))) :=
      (X_pow_sub_C_irreducible_iff_of_prime hq).mpr hnopow
    have hpoly :
        (((X : ℚ[X]) ^ q - C (A : ℚ)).map (algebraMap ℚ ℚ⟮α⟯) -
          C (AdjoinSimple.gen ℚ α)) =
        (X : ℚ⟮α⟯[X]) ^ q - C ((A : ℚ⟮α⟯) - (-AdjoinSimple.gen ℚ α)) := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_intCast, map_intCast, sub_neg_eq_add, map_add, sub_sub]
    rw [hpoly]
    exact hbin
  simpa only [composition_identity p q k A] using hcomp

/-- The stated numerical scope indeed makes both primes odd. -/
theorem scoped_prime_parities
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p) (hpq : p < q) :
    Odd p ∧ Odd q := by
  have h2p : 2 < p := lt_of_lt_of_le (by decide : 2 < 5) hp5
  exact ⟨hp.odd_of_ne_two (ne_of_gt h2p),
    hq.odd_of_ne_two (ne_of_gt (lt_trans h2p hpq))⟩

/-- SCOPED HELPER ONLY, retaining the requested `p≥5`, `q>p`, and `|k|>1`
interface. The local/global arithmetic and real exclusion remain the explicit
`hexclude` dependency; the final theorem must derive it rather than assume it.
The absolute-value bound is not needed by the formal Capelli step itself. -/
theorem scoped_irreducible_of_reduced_affine_exclusion
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p) (hpq : p < q)
    (k A : ℤ) (_hk : 1 < |k|)
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (hexclude : ReducedAffineExclusion p q k A) :
    Irreducible (((X : ℚ[X]) ^ q - C (A : ℚ)) ^ p + C (k : ℚ)) := by
  exact irreducible_composition_of_reduced_affine_exclusion p q hp
    (scoped_prime_parities p q hp hq hp5 hpq).1 hq k A hirr hexclude

end PillaiCapelliBridge
