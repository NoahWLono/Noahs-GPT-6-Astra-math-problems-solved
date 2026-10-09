import BinarySmallCode

namespace BooleanANF
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {Y : Type*} [DecidableEq Y] [Fintype Y]

/-- Exact baseline for seven nonzero words in the dimension-three equality case. -/
theorem code_baseline_sum (D : Submodule F₂ (Y → F₂)) [Fintype D] :
    (∑ c : D, (if c = 0 then 0 else 4 : ℤ)) = 4 * ((Fintype.card D : ℤ) - 1) := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const]
  have hpos : 0 < Fintype.card D := Fintype.card_pos_iff.mpr ⟨(0 : D)⟩
  simp only [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ (0 : D)),
    Finset.card_univ, nsmul_eq_mul]
  rw [Nat.cast_sub (Nat.succ_le_of_lt hpos)]
  simp only [Nat.cast_one]
  ring

/-- Count codeword weights by evaluating one coordinate at a time. -/
theorem code_weight_upper (D : Submodule F₂ (Y → F₂)) [Fintype D]
    (E : Finset Y) (hvanish : ∀ f ∈ D, ∀ y, y ∉ E → f y = 0) :
    2 * (∑ c : D, (weight (c : Y → F₂) : ℤ)) ≤
      (E.card : ℤ) * (Fintype.card D : ℤ) := by
  classical
  let eval (y : Y) : D →+ F₂ :=
    { toFun := fun c => c.val y
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hswap : 2 * (∑ c : D, (weight (c : Y → F₂) : ℤ)) =
      ∑ y : Y, 2 * (weight (eval y) : ℤ) := by
    simp only [weight, Nat.cast_sum, eval]
    rw [Finset.sum_comm, Finset.mul_sum]
    rfl
  rw [hswap]
  have heval (y : Y) : 2 * (weight (eval y) : ℤ) ≤
      if y ∈ E then (Fintype.card D : ℤ) else 0 := by
    by_cases hy : y ∈ E
    · rw [if_pos hy]
      exact additive_character_weight_bound (eval y)
    · rw [if_neg hy]
      have hezero : (eval y : D → F₂) = fun _ => 0 := by
        funext c
        exact hvanish c c.property y hy
      simp [hezero, weight]
  have h := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset Y)) => heval y)
  simpa [Finset.sum_ite, nsmul_eq_mul] using h

/-- Equality forces exactly seven support coordinates and weight four for every nonzero word. -/
theorem small_code_dimension_three (D : Submodule F₂ (Y → F₂))
    (E : Finset Y) (hE : E.card ≤ 7)
    (hvanish : ∀ f ∈ D, ∀ y, y ∉ E → f y = 0)
    (hmin : ∀ f ∈ D, f ≠ 0 → 4 ≤ weight f)
    (hdim : Module.finrank F₂ D = 3) :
    E.card = 7 ∧ ∀ f ∈ D, f ≠ 0 → weight f = 4 := by
  classical
  letI := Fintype.ofFinite D
  have hN : Fintype.card D = 8 := by
    simpa [ZMod.card, hdim] using (Module.card_eq_pow_finrank (K := F₂) (V := D))
  have hrow (c : D) : (if c = 0 then 0 else 4 : ℤ) ≤ (weight (c : Y → F₂) : ℤ) := by
    split_ifs with h
    · exact Int.natCast_nonneg _
    · have hn : (c : Y → F₂) ≠ 0 := fun hc => h (Subtype.ext hc)
      exact_mod_cast hmin c c.property hn
  have hlo := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset D)) => hrow c)
  rw [code_baseline_sum, hN] at hlo
  have hup := code_weight_upper D E hvanish
  rw [hN] at hup
  have hT : (∑ c : D, (weight (c : Y → F₂) : ℤ)) = 28 := by omega
  refine ⟨by omega, ?_⟩
  intro f hf hn
  let c : D := ⟨f,hf⟩
  have hc : c ≠ 0 := fun h => hn (congrArg Subtype.val h)
  have hd := Finset.single_le_sum
    (fun w (_ : w ∈ (Finset.univ : Finset D)) => sub_nonneg.mpr (hrow w))
    (Finset.mem_univ c)
  rw [Finset.sum_sub_distrib, code_baseline_sum, hN, hT, if_neg hc] at hd
  change (weight f : ℤ) - 4 ≤ _ at hd
  have hm := hmin f hf hn
  omega

/-- The only possible multiplicities of the three nonzero two-dimensional columns. -/
theorem two_dimensional_pattern_counts (n10 n01 n11 : ℕ)
    (hsize : n10+n01+n11 ≤ 7)
    (h1 : n10+n11 = 4 ∨ n10+n11 = 6)
    (h2 : n01+n11 = 4 ∨ n01+n11 = 6)
    (h3 : n10+n01 = 4 ∨ n10+n01 = 6) :
    (n10=2 ∧ n01=2 ∧ n11=2) ∨
    (n10=1 ∧ n01=3 ∧ n11=3) ∨
    (n10=3 ∧ n01=1 ∧ n11=3) ∨
    (n10=3 ∧ n01=3 ∧ n11=1) := by omega

/-- Seven weight-four character equations force every nonzero three-bit column once. -/
theorem three_dimensional_pattern_counts (a b c d e f g : ℕ)
    (h1 : a+c+e+g=4) (h2 : b+c+f+g=4) (h3 : d+e+f+g=4)
    (h12 : a+b+e+f=4) (h13 : a+c+d+f=4)
    (h23 : b+c+d+e=4) (h123 : a+b+d+g=4) :
    a=1 ∧ b=1 ∧ c=1 ∧ d=1 ∧ e=1 ∧ f=1 ∧ g=1 := by omega

end BooleanANF
