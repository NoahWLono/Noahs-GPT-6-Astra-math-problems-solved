import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Order.Ring.Int

/-!
Elaborated with pinned Lean 4.32.2 and mathlib commit
905b95818eb32af7874a58b427f50c1711a5e96c.
A generic actual-quotient conductor lemma. All monic-basis/field obligations are
unnecessary here: every quotient element has a polynomial representative, and
all sufficiently large powers belong to the smaller algebra by the trusted
natural-number coin lemma. Exact types, standard-axioms audits, resource records, and verification limits
are recorded alongside the clean build.
-/
set_option autoImplicit false
open Polynomial Algebra
namespace PillaiParameterConductor
universe u
variable {D : Type u} [CommRing D]

/-- Actual quotient conductor. No DVR, domain or unit hypothesis on `v` is
needed for this algebraic inclusion. `c` is a scalar unit. -/
theorem quotient_conductor
    (n r : ℕ) (hcop : n.Coprime r)
    (ell v : D) (c : Dˣ) :
    let f : D[X] := X ^ n - C (ell * v)
    let τ : AdjoinRoot f := AdjoinRoot.root f
    let R := Algebra.adjoin D ({algebraMap D (AdjoinRoot f) (c : D) * τ ^ r} :
      Set (AdjoinRoot f))
    ∀ z : AdjoinRoot f,
      z ∈ (Ideal.span {τ}) ^ ((n - 1) * (r - 1)) → z ∈ R := by
  dsimp only
  let f : D[X] := X ^ n - C (ell * v)
  let τ : AdjoinRoot f := AdjoinRoot.root f
  let R := Algebra.adjoin D ({algebraMap D (AdjoinRoot f) (c : D) * τ ^ r} :
    Set (AdjoinRoot f))
  let N := (n - 1) * (r - 1)
  change ∀ z : AdjoinRoot f, z ∈ (Ideal.span {τ}) ^ N → z ∈ R
  have hτ : τ ^ n = algebraMap D (AdjoinRoot f) (ell * v) := by
    apply sub_eq_zero.mp
    simpa only [f, τ, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
      AdjoinRoot.algebraMap_eq] using AdjoinRoot.eval₂_root f
  have hnmem : τ ^ n ∈ R := by
    rw [hτ]
    exact R.algebraMap_mem _
  have hrmem : τ ^ r ∈ R := by
    have ht : algebraMap D (AdjoinRoot f) (c : D) * τ ^ r ∈ R :=
      Algebra.self_mem_adjoin_singleton D _
    have hh := R.mul_mem (R.algebraMap_mem ((c⁻¹ : Dˣ) : D)) ht
    simpa only [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] using hh
  have hpow (k : ℕ) (hk : N ≤ k) : τ ^ k ∈ R := by
    obtain ⟨a, b, hab⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le
      n r k (by simp [hcop.gcd_eq_one]) (by simpa only [Nat.pred_eq_sub_one] using hk)
    have hh := R.mul_mem (R.pow_mem hnmem a) (R.pow_mem hrmem b)
    rw [← pow_mul, ← pow_mul, ← pow_add, Nat.mul_comm n a, Nat.mul_comm r b, hab] at hh
    exact hh
  have hmul (P : D[X]) : τ ^ N * AdjoinRoot.mk f P ∈ R := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
        simpa only [map_add, mul_add] using R.add_mem hP hQ
    | monomial j d =>
        rw [← AdjoinRoot.aeval_eq]
        have hh := R.mul_mem (R.algebraMap_mem d) (hpow (N + j) (Nat.le_add_right _ _))
        convert hh using 1
        simp only [aeval_monomial, pow_add]
        ring
  intro z hz
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective x
  exact hmul P

end PillaiParameterConductor
