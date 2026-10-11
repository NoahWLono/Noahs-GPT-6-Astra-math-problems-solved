import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring

/-! Fixed finite fibers of reduced degree-one rational functions. The affine
case has the fixed fiber at infinity; a linear denominator gives a finite
fixed point over the algebraically closed constant field, in every characteristic. -/
namespace Astra01
open Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]

theorem linear_polynomial_root_factor (p : k[X]) (hp : p.natDegree = 1)
    (c : k) (hc : p.eval c = 0) :
    p = C (p.coeff 1) * (X - C c) ∧ p.coeff 1 ≠ 0 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have heq := eq_X_add_C_of_natDegree_le_one hp.le
  have he : p.coeff 1 * c + p.coeff 0 = 0 := by
    have h := (congrArg (Polynomial.eval c) heq).symm.trans hc
    simpa only [eval_add, eval_mul, eval_C, eval_X] using h
  constructor
  · have h0 : p.coeff 0 = -(p.coeff 1 * c) := eq_neg_of_add_eq_zero_right he
    calc
      p = C (p.coeff 1) * X + C (p.coeff 0) := heq
      _ = C (p.coeff 1) * (X - C c) := by rw [h0, map_neg, map_mul]; ring
  · rw [← hp, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp0

theorem exists_fixed_linear_fiber (p q : k[X])
    (hpq : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 1)
    (hq : q.natDegree = 1) :
    ∃ c : k, (p - C c * q).eval c = 0 ∧
      (p - C c * q).natDegree = 1 ∧ IsCoprime (p - C c * q) q := by
  have hpdeg : p.natDegree ≤ 1 := by omega
  let s := p - X * q
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  have hxq : (X * q).natDegree = 2 := by rw [natDegree_X_mul hq0, hq]
  have hs : s.natDegree = 2 := by
    exact (natDegree_sub_eq_right_of_natDegree_lt (by omega)).trans hxq
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root s (by
    intro hz
    have hh : s.natDegree = 0 := natDegree_eq_of_degree_eq_some hz
    omega)
  have htroot : (p - C c * q).eval c = 0 := by
    simpa only [s, IsRoot, eval_sub, eval_mul, eval_X, eval_C] using hc
  have hcop : IsCoprime (p - C c * q) q := by
    simpa only [neg_mul, sub_eq_add_neg] using hpq.add_mul_right_left (-C c)
  have ht0 : p - C c * q ≠ 0 := by
    intro h
    have hunit : IsUnit q := by simpa only [h, isCoprime_zero_left] using hcop
    have hd : q.natDegree = 0 := natDegree_eq_of_degree_eq_some (degree_eq_zero_of_isUnit hunit)
    omega
  have htle : (p - C c * q).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le hpdeg ((natDegree_C_mul_le _ _).trans hq.le))
  have htne : (p - C c * q).natDegree ≠ 0 := by
    intro ht
    have he := eq_C_of_natDegree_eq_zero ht
    have hc0 : (p - C c * q).coeff 0 = 0 := by
      have h := (congrArg (Polynomial.eval c) he).symm.trans htroot
      simpa only [eval_C] using h
    apply ht0
    exact he.trans (by rw [hc0, C_0])
  exact ⟨c, htroot, by omega, hcop⟩

end Astra01
#print axioms Astra01.exists_fixed_linear_fiber
