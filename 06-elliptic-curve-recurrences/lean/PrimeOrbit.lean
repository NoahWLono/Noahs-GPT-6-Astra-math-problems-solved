import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! ASTRA-01 claim T6. This is a universal theorem about deterministic maps,
not a finite sample. Recurrence is assumed only up to the closing index n;
nonconstancy is explicitly inside the first n entries. -/
namespace Astra01

theorem prime_recurrence_injective {α : Type*} (T : α → α) (z : ℕ → α)
    (n : ℕ) (hn : n.Prime)
    (hstep : ∀ i < n, z (i+1) = T (z i))
    (hclose : z n = z 0)
    (hnonconstant : ∃ i < n, z i ≠ z 0) :
    Function.Injective (fun i : Fin n => z i.val) := by
  have hz : ∀ i, i ≤ n → z i = T^[i] (z 0) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [hstep i (Nat.lt_of_succ_le hi), ih (Nat.le_of_succ_le hi)]
      exact (Function.iterate_succ_apply' T i (z 0)).symm
  have hper : Function.IsPeriodicPt T n (z 0) := by
    change T^[n] (z 0) = z 0
    rw [← hz n (Nat.le_refl n)]
    exact hclose
  have hnotfixed : ¬Function.IsFixedPt T (z 0) := by
    intro hfixed
    obtain ⟨i, hi, hne⟩ := hnonconstant
    apply hne
    rw [hz i hi.le]
    exact hfixed.iterate i
  letI : Fact n.Prime := ⟨hn⟩
  have hperiod : Function.minimalPeriod T (z 0) = n :=
    Function.minimalPeriod_eq_prime hper hnotfixed
  intro i j hij
  apply Fin.ext
  have hi : i.val < Function.minimalPeriod T (z 0) := by simpa only [hperiod] using i.isLt
  have hj : j.val < Function.minimalPeriod T (z 0) := by simpa only [hperiod] using j.isLt
  apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp
  rw [← hz i.val i.isLt.le, ← hz j.val j.isLt.le]
  exact hij

#print axioms prime_recurrence_injective
end Astra01
