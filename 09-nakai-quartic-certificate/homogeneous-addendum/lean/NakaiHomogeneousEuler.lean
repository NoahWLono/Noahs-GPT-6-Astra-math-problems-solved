import NakaiHomogeneousDefinitions
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Euler and cofactor identities. No isolatedness or socle theorem is assumed. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NakaiHomogeneous
open NakaiFramework
variable {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
variable (f : P (k := k) (ι := ι)) (d : ℕ)

omit [CharZero k] [DecidableEq ι] in
theorem euler_f (hf : f.IsHomogeneous d) :
    (∑ i, X i * pderiv i f) = (d : P (k := k) (ι := ι)) * f := by
  simpa only [nsmul_eq_mul] using hf.sum_X_mul_pderiv

omit [Fintype ι] [DecidableEq ι] in
theorem degree_pred_ne_zero (hd : 2 ≤ d) :
    (d : P (k := k) (ι := ι)) - 1 ≠ 0 := by
  apply sub_ne_zero.mpr
  have hn : d ≠ 1 := ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hd)
  simpa only [Nat.cast_one] using (Nat.cast_injective (R := P (k := k) (ι := ι))).ne hn

omit [CharZero k] in
theorem H_mul_X (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (i : ι) :
    (∑ j, H f i j * X j) = ((d : P (k := k) (ι := ι)) - 1) * pderiv i f := by
  have hp := (hf.pderiv (i := i)).sum_X_mul_pderiv
  have hd1 : 1 ≤ d := le_trans (by decide : 1 ≤ 2) hd
  rw [nsmul_eq_mul, Nat.cast_sub hd1, Nat.cast_one] at hp
  rw [← hp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [H, pderiv_comm i j f, mul_comm]

theorem degree_mul_U_grad (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (i : ι) :
    ((d : P (k := k) (ι := ι)) - 1) * (∑ j, U f i j * pderiv j f) = h f * X i := by
  calc
    _ = ∑ j, U f i j * (((d : P (k := k) (ι := ι)) - 1) * pderiv j f) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j, U f i j * ∑ l, H f j l * X l := by simp_rw [H_mul_X f d hf hd]
    _ = ∑ l, (∑ j, U f i j * H f j l) * X l := by
      simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by simp [U_mul_H, ite_mul]

theorem degree_mul_Ucol_grad (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (r : ι) :
    ((d : P (k := k) (ι := ι)) - 1) * (∑ i, U f i r * pderiv i f) = h f * X r := by
  simp_rw [U_symmetric f _ r]
  exact degree_mul_U_grad f d hf hd r

omit [CharZero k] in
theorem B_mul_grad_expansion (r i : ι) :
    (∑ j, B f r i j * pderiv j f) =
      U f i r * (∑ j, X j * pderiv j f) +
      X i * (∑ j, U f j r * pderiv j f) -
      X r * (∑ j, U f i j * pderiv j f) := by
  simp only [B, add_mul, sub_mul, mul_assoc, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem B_mul_grad (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (r i : ι) :
    (∑ j, B f r i j * pderiv j f) = (d : P (k := k) (ι := ι)) * f * U f i r := by
  apply mul_left_cancel₀ (degree_pred_ne_zero (k := k) (ι := ι) d hd)
  rw [B_mul_grad_expansion, euler_f f d hf]
  calc
    _ = ((d : P (k := k) (ι := ι)) - 1) * ((d : P (k := k) (ι := ι)) * f * U f i r) +
        X i * (((d : P (k := k) (ι := ι)) - 1) * (∑ j, U f j r * pderiv j f)) -
        X r * (((d : P (k := k) (ι := ι)) - 1) * (∑ j, U f i j * pderiv j f)) := by ring
    _ = _ := by
      rw [degree_mul_Ucol_grad f d hf hd r, degree_mul_U_grad f d hf hd i]
      ring

#print axioms degree_mul_U_grad
#print axioms B_mul_grad
end NakaiHomogeneous
