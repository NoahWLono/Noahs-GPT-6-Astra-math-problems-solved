import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.FieldTheory.Finite.Basic

/-! Necessary prime-period alternatives for every genuine GL₂(K) group action.
This is a general finite-field theorem, not an assumed classification.
The projective-line action/representative bridge is a separate obligation.
The theorem does NOT claim that a representing matrix has exact order n,
nor that the induced projective map has exact order n. -/
namespace Astra01
open scoped MatrixGroups

/-- A nonfixed prime-period point in any action of GL₂(K) forces the field
alternatives used by ASTRA-01. The acted-on type need not itself be finite. -/
theorem prime_period_gl2_field_alternatives
    {K α : Type*} [Field K] [Fintype K] [MulAction (GL (Fin 2) K) α]
    (M : GL (Fin 2) K) (x : α) (n : ℕ) (hn : n.Prime)
    (hcycle : M^n • x = x) (hnotfixed : M • x ≠ x) :
    n = ringChar K ∨ n ∣ Fintype.card K - 1 ∨ n ∣ Fintype.card K + 1 := by
  letI : Fact n.Prime := ⟨hn⟩
  have hp : Function.IsPeriodicPt (M • ·) n x :=
    MulAction.isPeriodicPt_smul_iff.mpr hcycle
  have hperiod : Function.minimalPeriod (M • ·) x = n :=
    Function.minimalPeriod_eq_prime hp hnotfixed
  have horder : n ∣ orderOf M := by
    rw [← hperiod, ← MulAction.pow_smul_eq_iff_minimalPeriod_dvd]
    rw [pow_orderOf_eq_one, one_smul]
  have hdvd : n ∣ Nat.card (GL (Fin 2) K) :=
    horder.trans (orderOf_dvd_natCard M)
  let q := Fintype.card K
  have hq : 1 ≤ q := Fintype.card_pos
  have hqq : 1 ≤ q*q := by simpa using Nat.mul_le_mul hq hq
  have hfac1 : q^2-1 = (q-1)*(q+1) := by
    rw [Nat.sub_mul, Nat.mul_add, Nat.one_mul, pow_two]
    omega
  have hfac2 : q^2-q = q*(q-1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_two]
  have hcard : Nat.card (GL (Fin 2) K) = (q^2-1)*(q^2-q) := by
    simpa [Fin.prod_univ_two, q] using (Matrix.card_GL_field (𝔽 := K) 2)
  rw [hcard, hfac1, hfac2] at hdvd
  rcases hn.dvd_mul.mp hdvd with hleft | hright
  · rcases hn.dvd_mul.mp hleft with hminus | hplus
    · exact Or.inr (Or.inl hminus)
    · exact Or.inr (Or.inr hplus)
  · rcases hn.dvd_mul.mp hright with hchar | hminus
    · obtain ⟨e, hpchar, hsize⟩ := FiniteField.card K (ringChar K)
      left
      exact Nat.prime_eq_prime_of_dvd_pow hn hpchar (by simpa only [q, hsize] using hchar)
    · exact Or.inr (Or.inl hminus)

/-- The same necessary alternatives, with exactly the bounded recurrence,
closure, and within-orbit nonconstancy hypotheses used in the paper. -/
theorem prime_recurrence_gl2_field_alternatives
    {K α : Type*} [Field K] [Fintype K] [MulAction (GL (Fin 2) K) α]
    (M : GL (Fin 2) K) (z : ℕ → α) (n : ℕ) (hn : n.Prime)
    (hstep : ∀ i < n, z (i+1) = M • z i)
    (hclose : z n = z 0) (hnonconstant : ∃ i < n, z i ≠ z 0) :
    n = ringChar K ∨ n ∣ Fintype.card K - 1 ∨ n ∣ Fintype.card K + 1 := by
  have hz : ∀ i, i ≤ n → z i = M^i • z 0 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [hstep i (Nat.lt_of_succ_le hi), ih (Nat.le_of_succ_le hi)]
      simp [pow_succ', mul_smul]
  have hcycle : M^n • z 0 = z 0 := by rw [← hz n (Nat.le_refl n)]; exact hclose
  have hnotfixed : M • z 0 ≠ z 0 := by
    intro hfix
    have hconst : ∀ i, i ≤ n → z i = z 0 := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        rw [hstep i (Nat.lt_of_succ_le hi), ih (Nat.le_of_succ_le hi), hfix]
    obtain ⟨i, hi, hne⟩ := hnonconstant
    exact hne (hconst i hi.le)
  exact prime_period_gl2_field_alternatives M (z 0) n hn hcycle hnotfixed

#print axioms prime_recurrence_gl2_field_alternatives
#print axioms prime_period_gl2_field_alternatives
end Astra01
