import BooleanANFWeight
import Mathlib.Algebra.Group.Equiv.Basic

namespace BooleanANF
open scoped BigOperators
variable {A : Type*} [AddGroup A] [Fintype A]

/-- Boolean additive derivative, retaining actual function semantics. -/
def derivative (f : A → F₂) (a x : A) : F₂ := f (x + a) + f x

theorem weight_translate (f : A → F₂) (a : A) :
    weight (fun x => f (x + a)) = weight f := by
  exact weight_equiv f (Equiv.addRight a)

private theorem bit_mul_nat (a b : F₂) : (a*b).val = a.val*b.val := by
  fin_cases a <;> fin_cases b <;> decide

/-- Count every ordered pair of support points once through its displacement. -/
theorem sum_intersection_weights (f : A → F₂) :
    (∑ a, weight (fun x => f (x+a) * f x)) = weight f * weight f := by
  unfold weight
  rw [Finset.sum_comm]
  simp_rw [bit_mul_nat, ← Finset.sum_mul]
  have hs (x : A) : (∑ a, (f (x+a)).val) = ∑ a, (f a).val :=
    Equiv.sum_comp (Equiv.addLeft x) (fun a => (f a).val)
  simp_rw [hs]
  exact (Finset.mul_sum _ _ _).symm

/-- The derivative-weight identity used by the low-weight residue exclusion. -/
theorem derivative_weight_sum (f : A → F₂) :
    (∑ a : A, (weight (derivative f a) : ℤ)) =
      2 * (weight f : ℤ) * ((Fintype.card A : ℤ) - (weight f : ℤ)) := by
  have h (a : A) : (weight (derivative f a) : ℤ) =
      2 * (weight f : ℤ) - 2 * (weight (fun x => f (x+a)*f x) : ℤ) := by
    change (weight (fun x => f (x+a) + f x) : ℤ) = _
    rw [weight_add, weight_translate]
    ring
  simp_rw [h]
  have hs : (∑ a : A, 2 * (weight (fun x => f (x+a)*f x) : ℤ)) =
      2 * ((weight f : ℤ) * (weight f : ℤ)) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, sum_intersection_weights, Nat.cast_mul]
  rw [Finset.sum_sub_distrib, hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end BooleanANF
