import BooleanANFSupportBounds
import Mathlib.GroupTheory.Coset.Card

namespace BooleanANF
open scoped BigOperators
variable {A : Type*} [AddGroup A] [Fintype A]

/-- The genuine group of translations preserving a Boolean function. -/
def translationStabilizer (f : A → F₂) : AddSubgroup A where
  carrier := {a | ∀ x, f (x+a) = f x}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x
    rw [← add_assoc, hb, ha]
  neg_mem' := by
    intro a ha x
    have h := ha (x + -a)
    simpa using h.symm

@[simp] theorem mem_translationStabilizer (f : A → F₂) (a : A) :
    a ∈ translationStabilizer f ↔ ∀ x, f (x+a) = f x := Iff.rfl

theorem derivative_weight_zero_iff_stabilizer (f : A → F₂) (a : A) :
    weight (derivative f a) = 0 ↔ a ∈ translationStabilizer f := by
  rw [weight_eq_zero_iff]
  constructor
  · intro h x
    have hx := congrFun h x
    change f (x+a) + f x = 0 at hx
    have hxx := CharTwo.add_self_eq_zero (f x)
    exact add_right_cancel (hx.trans hxx.symm)
  · intro h
    funext x
    change f (x+a) + f x = 0
    rw [h x, CharTwo.add_self_eq_zero]

theorem translationStabilizer_card_dvd (f : A → F₂) :
    Nat.card (translationStabilizer f) ∣ Fintype.card A := by
  simpa [Nat.card_eq_fintype_card] using
    (translationStabilizer f).card_addSubgroup_dvd_card

theorem translationStabilizer_card_le (f : A → F₂) :
    Nat.card (translationStabilizer f) ≤ Fintype.card A := by
  classical
  letI : Fintype (translationStabilizer f) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_le _

/-- A two-valued derivative spectrum is counted by the actual translation subgroup. -/
theorem derivative_stabilizer_count (f : A → F₂) (k : ℕ)
    (hk : ∀ a, weight (derivative f a) = 0 ∨ weight (derivative f a) = k) :
    (k : ℤ) * ((Fintype.card A : ℤ) - Nat.card (translationStabilizer f)) =
      2 * (weight f : ℤ) * ((Fintype.card A : ℤ) - weight f) := by
  classical
  letI : Fintype (translationStabilizer f) := Fintype.ofFinite _
  have he (a : A) : (weight (derivative f a) : ℤ) =
      k - if a ∈ translationStabilizer f then (k : ℤ) else 0 := by
    by_cases ha : a ∈ translationStabilizer f
    · simp [ha, (derivative_weight_zero_iff_stabilizer f a).mpr ha]
    · have h := (hk a).resolve_left (fun hz => ha
        ((derivative_weight_zero_iff_stabilizer f a).mp hz))
      simp [ha, h]
  have hcard : (Finset.univ.filter (fun a => a ∈ translationStabilizer f)).card =
      Nat.card (translationStabilizer f) := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  have hs := derivative_weight_sum f
  simp_rw [he] at hs
  rw [Finset.sum_sub_distrib] at hs
  have hind : (∑ a : A, if a ∈ translationStabilizer f then (k : ℤ) else 0) =
      (Nat.card (translationStabilizer f) : ℤ) * k := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, hcard]
    simp only [nsmul_eq_mul]
  rw [hind] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  calc
    (k : ℤ) * ((Fintype.card A : ℤ) - Nat.card (translationStabilizer f)) =
      (Fintype.card A : ℤ) * k - (Nat.card (translationStabilizer f) : ℤ) * k := by ring
    _ = _ := hs

end BooleanANF
