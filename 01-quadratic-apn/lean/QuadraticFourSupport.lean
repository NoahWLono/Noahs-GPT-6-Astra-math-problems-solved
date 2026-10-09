import QuadraticFourCertificates
import Mathlib.Algebra.BigOperators.Pi

set_option maxHeartbeats 1200000
namespace BooleanANF.QuadraticFour
open scoped BigOperators

def supportPoints (f : V → F₂) : Finset V := Finset.univ.filter (fun x => f x = 1)

/-- A degree-two truth table has zero first moment over the binary cube. -/
theorem support_sum_zero {f : V → F₂} (hf : HasDegreeLE f 2) :
    ∑ x ∈ supportPoints f, x = 0 := by
  ext i
  simp only [Finset.sum_apply, Pi.zero_apply]
  calc
    ∑ x ∈ supportPoints f, x i = ∑ x, f x * x i := by
      simp only [supportPoints, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      generalize f x = a
      fin_cases a <;> simp
    _ = coefficient (fun x => f x * x i) Finset.univ := (coefficient_top_eq_sum _).symm
    _ = 0 := (hf.mul (degree_coordinate i)) _ (by norm_num)

/-- Every weight-four quadratic support is a parallelogram of four distinct
points; this is an affine two-plane over F₂, with no finite enumeration needed. -/
theorem support_four_parallelogram {f : V → F₂} (hf : HasDegreeLE f 2)
    (hw : weight f = 4) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      supportPoints f = {a, b, c, a + b + c} := by
  have hc : (supportPoints f).card = 4 := by
    change (Finset.univ.filter (fun x => f x = 1)).card = 4
    rw [← weight_eq_support_card]
    exact hw
  obtain ⟨a, t, ha, ht, htc⟩ := Finset.card_eq_succ.mp hc
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp htc
  have hab : a ≠ b := by
    intro h
    apply ha
    simp [h]
  have hac : a ≠ c := by
    intro h
    apply ha
    simp [h]
  have had : a ≠ d := by
    intro h
    apply ha
    simp [h]
  have hs := support_sum_zero hf
  rw [← ht] at hs
  simp only [Finset.sum_insert ha, Finset.sum_insert (by simp [hbc, hbd] : b ∉ ({c,d} : Finset V)),
    Finset.sum_insert (by simp [hcd] : c ∉ ({d} : Finset V)), Finset.sum_singleton] at hs
  have hd : d = a + b + c := by
    calc
      d = (a+a) + (b+b) + (c+c) + d := by
        ext i
        simp [Pi.add_apply, CharTwo.add_self_eq_zero]
      _ = (a + (b + (c + d))) + (a + b + c) := by abel
      _ = a + b + c := by rw [hs, zero_add]
  exact ⟨a, b, c, hab, hac, hbc, by rw [← ht, hd]⟩

end BooleanANF.QuadraticFour
