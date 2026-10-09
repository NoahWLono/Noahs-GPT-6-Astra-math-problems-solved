import BooleanANFDerivativeWeight
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace BooleanANF
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A nonzero binary additive character is balanced; zero characters have smaller weight. -/
theorem additive_character_weight_bound {A : Type*} [AddGroup A] [Fintype A]
    (L : A →+ F₂) : 2 * (weight L : ℤ) ≤ (Fintype.card A : ℤ) := by
  classical
  by_cases hz : L = 0
  · subst L
    simp [weight]
  · have ha : ∃ a, L a ≠ 0 := by
      by_contra h
      apply hz
      ext a
      simpa using (not_exists.mp h a)
    obtain ⟨a, ha⟩ := ha
    have ha1 : L a = 1 := by
      generalize L a = b at *
      fin_cases b <;> simp_all
    have ht := weight_translate (fun x => L x) a
    have hrepr : (fun x => L (x+a)) = fun x => L x + 1 := by
      funext x
      simp [map_add, ha1]
    rw [hrepr] at ht
    have hs := weight_add (fun x => L x) (fun _ => (1 : F₂))
    have hw1 : weight (fun _ : A => (1 : F₂)) = Fintype.card A := by
      simp only [weight, show (1 : F₂).val = 1 from rfl, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, mul_one]
    simp only [mul_one] at hs
    rw [hw1, ht] at hs
    change 2 * (weight (fun x => L x) : ℤ) ≤ (Fintype.card A : ℤ)
    omega

/-- Binary linear codes supported on seven coordinates, with distance at least four,
have dimension at most three. This is the exact Plotkin double-count used in the classification. -/
theorem small_code_finrank_le_three {Y : Type*} [DecidableEq Y] [Fintype Y]
    (D : Submodule F₂ (Y → F₂)) (E : Finset Y) (hE : E.card ≤ 7)
    (hvanish : ∀ f ∈ D, ∀ y, y ∉ E → f y = 0)
    (hmin : ∀ f ∈ D, f ≠ 0 → 4 ≤ weight f) :
    Module.finrank F₂ D ≤ 3 := by
  classical
  letI := Fintype.ofFinite D
  let N : ℕ := Fintype.card D
  let T : ℤ := ∑ c : D, (weight (c : Y → F₂) : ℤ)
  have hrow (c : D) : (if c = 0 then 0 else 4 : ℤ) ≤ (weight (c : Y → F₂) : ℤ) := by
    split_ifs with h
    · exact Int.natCast_nonneg _
    · have hn : (c : Y → F₂) ≠ 0 := by
        intro hc
        apply h
        exact Subtype.ext hc
      exact_mod_cast hmin c c.property hn
  have hlower : 4 * ((N : ℤ) - 1) ≤ T := by
    have h := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset D)) => hrow c)
    have he : (∑ c : D, (if c = 0 then 0 else 4 : ℤ)) = 4 * ((N : ℤ) - 1) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const]
      have hpos : 0 < Fintype.card D := Fintype.card_pos_iff.mpr ⟨(0 : D)⟩
      simp only [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ (0 : D)),
        Finset.card_univ, nsmul_eq_mul]
      rw [Nat.cast_sub (Nat.succ_le_of_lt hpos)]
      simp only [Nat.cast_one, N]
      ring
    rw [he] at h
    exact h
  let eval (y : Y) : D →+ F₂ :=
    { toFun := fun c => c.val y
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hswap : 2 * T = ∑ y : Y, 2 * (weight (eval y) : ℤ) := by
    simp only [T, weight, Nat.cast_sum, eval]
    rw [Finset.sum_comm, Finset.mul_sum]
    rfl
  have heval (y : Y) : 2 * (weight (eval y) : ℤ) ≤ if y ∈ E then (N : ℤ) else 0 := by
    by_cases hy : y ∈ E
    · rw [if_pos hy]
      exact additive_character_weight_bound (eval y)
    · rw [if_neg hy]
      have hezero : (eval y : D → F₂) = fun _ => 0 := by
        funext c
        exact hvanish c c.property y hy
      simp [hezero, weight]
  have hupper : 2 * T ≤ (E.card : ℤ) * N := by
    rw [hswap]
    have h := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset Y)) => heval y)
    simpa [Finset.sum_ite, nsmul_eq_mul] using h
  have hN : N ≤ 8 := by
    have hN0 : (0 : ℤ) ≤ N := Int.natCast_nonneg _
    have hEint : (E.card : ℤ) ≤ 7 := by exact_mod_cast hE
    have hu := le_trans hupper (mul_le_mul_of_nonneg_right hEint hN0)
    omega
  have hpow : N = 2 ^ Module.finrank F₂ D := by
    simpa [N, ZMod.card] using (Module.card_eq_pow_finrank (K := F₂) (V := D))
  by_contra hdim
  have hp : 16 ≤ 2 ^ Module.finrank F₂ D :=
    show 2 ^ 4 ≤ 2 ^ Module.finrank F₂ D from
      Nat.pow_le_pow_right (by decide : 0 < 2) (show 4 ≤ Module.finrank F₂ D by omega)
  omega

end BooleanANF
