import SingletonShear
import Mathlib.Logic.Equiv.Prod

set_option maxHeartbeats 1200000

namespace BooleanANF
open scoped BigOperators

/-- Hamming weight, computably summing the standard zero/one lifts. -/
def weight {α : Type*} [Fintype α] (f : α → F₂) : ℕ := ∑ x, (f x).val

theorem weight_eq_support_card {α : Type*} [Fintype α] (f : α → F₂) :
    weight f = (Finset.univ.filter (fun x => f x = 1)).card := by
  classical
  rw [weight, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  generalize f x = a
  fin_cases a <;> decide

theorem weight_equiv {α β : Type*} [Fintype α] [Fintype β]
    (f : β → F₂) (e : α ≃ β) : weight (fun x => f (e x)) = weight f :=
  e.sum_comp (fun x => (f x).val)

private theorem bit_add_int (a b : F₂) :
    ((a + b).val : ℤ) = (a.val : ℤ) + (b.val : ℤ) - 2 * ((a*b).val : ℤ) := by
  fin_cases a <;> fin_cases b <;> decide

/-- Exact XOR/intersection identity in integers, avoiding truncated subtraction. -/
theorem weight_add {α : Type*} [Fintype α] (f g : α → F₂) :
    (weight (fun x => f x + g x) : ℤ) = (weight f : ℤ) + (weight g : ℤ) -
      2 * (weight (fun x => f x * g x) : ℤ) := by
  simp only [weight, Nat.cast_sum]
  simp_rw [bit_add_int]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

@[simp] theorem weight_delta {ι : Type*} [DecidableEq ι] [Fintype ι] (a : ι → F₂) :
    weight (delta a) = 1 := by
  simp [weight, delta, apply_ite]
  rfl

theorem weight_mul_delta {ι : Type*} [DecidableEq ι] [Fintype ι]
    (f : (ι → F₂) → F₂) (a : ι → F₂) :
    weight (fun x => f x * delta a x) = (f a).val := by
  simp [weight, delta, mul_ite, apply_ite]

/-- Partitioning a Boolean truth table into fibers preserves its total weight. -/
theorem weight_fibers {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ]
    (f : ((ι ⊕ κ) → F₂) → F₂) :
    (∑ y : κ → F₂, weight (fun x => f (Sum.elim x y))) = weight f := by
  have h := (Equiv.sumArrowEquivProdArrow ι κ F₂).symm.sum_comp
    (fun z => (f z).val)
  rw [Fintype.sum_prod_type] at h
  change (∑ y, ∑ x, (f (Sum.elim x y)).val) = ∑ z, (f z).val
  rw [Finset.sum_comm]
  exact h

/-- The signed row cost used in the weight-thirty classification. -/
def cost {ι : Type*} [DecidableEq ι] [Fintype ι] (q : (ι → F₂) → F₂) : ℤ :=
  (weight q : ℤ) - 2 * ((q 0).val : ℤ)

theorem weight_add_delta_zero {ι : Type*} [DecidableEq ι] [Fintype ι]
    (q : (ι → F₂) → F₂) :
    (weight (fun x => q x + delta 0 x) : ℤ) = 1 + cost q := by
  rw [weight_add, weight_delta, weight_mul_delta]
  simp only [cost, Nat.cast_one]
  ring

def residual (f : DoubleBlock → F₂) (z : DoubleBlock) : F₂ :=
  normalized f z + delta 0 (fun i => z (.inl i))

theorem residual_fiber (f : DoubleBlock → F₂) (y : Block) :
    fiber (residual f) y = fun x => fiber (normalized f) y x + delta 0 x := rfl

theorem residual_degree {f : DoubleBlock → F₂} (hf : HasDegreeLE f 4) :
    HasDegreeLE (residual f) 4 := by
  apply (normalized_degree hf).add
  have hd : HasDegreeLE (delta (0 : Block)) 4 := by
    intro s hs
    have hc := Finset.card_le_univ s
    simp only [Fintype.card_fin] at hc
    omega
  exact hd.comp_affine (κ := Fin 4 ⊕ Fin 4) (fun z i => z (.inl i))
    (fun i => degree_coordinate (ι := Fin 4 ⊕ Fin 4) (.inl i))

theorem residual_sum_constant {f : DoubleBlock → F₂} (hf : HasDegreeLE f 4)
    (x : Block) :
    (∑ y : Block, fiber (residual f) y x) = ∑ y : Block, fiber (residual f) y 0 := by
  have hh := HasDegreeLE.sum_fibers (ι := Fin 4) (κ := Fin 4) (d := 0) (residual_degree hf)
  exact hh.eq_const x

theorem normalized_weight (f : DoubleBlock → F₂) : weight (normalized f) = weight f := by
  let e : DoubleBlock ≃ DoubleBlock :=
    ⟨shearMap f, shearMap f, shearMap_involutive f, shearMap_involutive f⟩
  exact weight_equiv f e

/-- The cost budget is an exact identity for every input function. -/
theorem residual_cost_sum (f : DoubleBlock → F₂) :
    (∑ y : Block, cost (fiber (residual f) y)) = (weight f : ℤ) - 16 := by
  have h (y : Block) :
      (weight (fiber (normalized f) y) : ℤ) = 1 + cost (fiber (residual f) y) := by
    rw [← weight_add_delta_zero]
    congr 2
    funext x
    simp [fiber, residual, add_assoc, CharTwo.add_self_eq_zero]
  have hs := congrArg (fun k : ℕ => (k : ℤ)) (weight_fibers (normalized f))
  simp only [Nat.cast_sum] at hs
  change (∑ y : Block, (weight (fiber (normalized f) y) : ℤ)) = _ at hs
  simp_rw [h] at hs
  rw [Finset.sum_add_distrib, normalized_weight] at hs
  norm_num [Fintype.card_fun, Block, ZMod.card] at hs
  omega

theorem residual_cost_fourteen {f : DoubleBlock → F₂} (hw : weight f = 30) :
    (∑ y : Block, cost (fiber (residual f) y)) = 14 := by
  rw [residual_cost_sum, hw]
  norm_num

end BooleanANF
