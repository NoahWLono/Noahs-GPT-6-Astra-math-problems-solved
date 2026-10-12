module
public import ZariskiBasic
public import Mathlib.Tactic.FieldSimp

@[expose] public section

noncomputable section
namespace ZariskiCylinder
open Polynomial
variable {k : Type*} [Field k]

/-- Polynomial in the displacement, including the regular value at displacement zero. -/
def divided (P : k[X]) (t : k) : k[X] := (P.comp (X + C t)).divX

/-- No division of field elements occurs in this definition. -/
def difference (P : k[X]) (t q s : k) : k := s * (divided P t).eval (q * s)

@[simp] theorem difference_zero (P : k[X]) (t q : k) : difference P t q 0 = 0 := by
  simp [difference]

theorem difference_mul (P : k[X]) (t q s : k) :
    P.eval (t + q * s) - P.eval t = q * difference P t q s := by
  have h := congrArg (fun f : k[X] => f.eval (q * s))
    (divX_mul_X_add (P.comp (X + C t)))
  simp only [eval_add, eval_mul, eval_X, eval_C, eval_comp, coeff_zero_eq_eval_zero] at h
  simp only [zero_add] at h
  unfold difference divided
  rw [add_comm t (q * s)]
  rw [← h]
  ring

@[simp] theorem difference_q_zero (P : k[X]) (t s : k) :
    difference P t 0 s = s * (divided P t).eval 0 := by simp [difference]

theorem difference_add (P : k[X]) (t q s r : k) :
    difference P t q (s + r) =
      difference P t q s + difference P (t + q * s) q r := by
  by_cases hq : q = 0
  · simp [hq, add_mul]
  · apply mul_left_cancel₀ hq
    rw [mul_add, ← difference_mul, ← difference_mul, ← difference_mul]
    have ha : t + q * (s + r) = t + q * s + q * r := by ring
    rw [ha]
    ring

theorem divided_eval_zero (P : k[X]) (t : k) :
    (divided P t).eval 0 = P.derivative.eval t := by
  have h := congrArg (fun f : k[X] => f.coeff 0) (derivative_comp P (X + C t))
  simp only [coeff_derivative, zero_add, Nat.cast_one, mul_one,
    derivative_add, derivative_X, derivative_C, add_zero, one_mul] at h
  unfold divided
  rw [← coeff_zero_eq_eval_zero, coeff_divX]
  simpa [coeff_zero_eq_eval_zero] using h

#print axioms difference_add
#print axioms divided_eval_zero
end ZariskiCylinder
