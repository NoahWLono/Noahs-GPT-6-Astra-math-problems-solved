import NakaiFramework
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
A characteristic-zero homogeneous variable-syzygy homotopy. This is a preliminary
algebraic lemma for a possible Hessian nonmembership bridge, not that bridge.
-/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NakaiVariableSyzygy
variable {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
abbrev P := MvPolynomial ι k

/-- Euler's explicit homotopy for a homogeneous relation among the variables. -/
theorem euler_syzygy_identity (u : ι → P (k := k) (ι := ι)) (m : ℕ)
    (hu : ∀ i, (u i).IsHomogeneous m) (hrel : ∑ i, u i * X i = 0) (j : ι) :
    ((m+1 : ℕ) : P (k := k) (ι := ι)) * u j =
      ∑ i, X i * (pderiv i (u j) - pderiv j (u i)) := by
  have he : (∑ i, X i * pderiv i (u j)) = (m : P (k := k) (ι := ι)) * u j := by
    simpa only [nsmul_eq_mul] using (hu j).sum_X_mul_pderiv
  have hd := congrArg (fun p : P (k := k) (ι := ι) => pderiv j p) hrel
  simp only [map_sum, pderiv_mul, pderiv_X, map_zero, Finset.sum_add_distrib] at hd
  have hx : (∑ i, u i * (Pi.single j 1 : ι → P (k := k) (ι := ι)) i) = u j := by
    simp [Pi.single_apply, mul_ite]
  rw [hx] at hd
  have hd' : (∑ i, X i * pderiv j (u i)) + u j = 0 := by
    simpa only [mul_comm] using hd
  calc
    _ = (m : P (k := k) (ι := ι)) * u j + u j := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    _ = (∑ i, X i * pderiv i (u j)) - (∑ i, X i * pderiv j (u i)) := by
      rw [he]
      have hs : (∑ i, X i * pderiv j (u i)) = -u j := eq_neg_of_add_eq_zero_left hd'
      rw [hs]
      ring
    _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib]

def coefficient (u : ι → P (k := k) (ι := ι)) (m : ℕ) (i j : ι) : P (k := k) (ι := ι) :=
  C (((m+1 : ℕ) : k)⁻¹) * (pderiv i (u j) - pderiv j (u i))

omit [CharZero k] [Fintype ι] [DecidableEq ι] in
theorem coefficient_skew (u : ι → P (k := k) (ι := ι)) (m : ℕ) (i j : ι) :
    coefficient u m i j = -coefficient u m j i := by
  simp only [coefficient]
  ring

theorem variable_syzygy (u : ι → P (k := k) (ι := ι)) (m : ℕ)
    (hu : ∀ i, (u i).IsHomogeneous m) (hrel : ∑ i, u i * X i = 0) (j : ι) :
    u j = ∑ i, coefficient u m i j * X i := by
  have hm : ((m+1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  calc
    u j = (C (((m+1 : ℕ) : k)⁻¹) * C ((m+1 : ℕ) : k)) * u j := by
      rw [← map_mul, inv_mul_cancel₀ hm, map_one, one_mul]
    _ = C (((m+1 : ℕ) : k)⁻¹) *
        (((m+1 : ℕ) : P (k := k) (ι := ι)) * u j) := by rw [map_natCast, mul_assoc]
    _ = C (((m+1 : ℕ) : k)⁻¹) *
        (∑ i, X i * (pderiv i (u j) - pderiv j (u i))) := by rw [euler_syzygy_identity u m hu hrel j]
    _ = _ := by
      simp only [Finset.mul_sum, coefficient]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The homogeneous syzygy homotopy applied to an arbitrary coordinate functional. -/
theorem syzygy_functional (u c : ι → P (k := k) (ι := ι)) (m : ℕ)
    (hu : ∀ i, (u i).IsHomogeneous m) (hrel : ∑ i, u i * X i = 0) :
    ((m+1 : ℕ) : P (k := k) (ι := ι)) * (∑ j, c j * u j) =
      ∑ i, ∑ j, pderiv i (u j) * (X i * c j - X j * c i) := by
  calc
    _ = ∑ j, c j * (((m+1 : ℕ) : P (k := k) (ι := ι)) * u j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j, ∑ i, (X i * c j * pderiv i (u j) - X i * c j * pderiv j (u i)) := by
      simp_rw [euler_syzygy_identity u m hu hrel, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, ∑ j, X i * c j * pderiv i (u j)) -
        (∑ i, ∑ j, X j * c i * pderiv i (u j)) := by
      simp only [Finset.sum_sub_distrib]
      rw [Finset.sum_comm (f := fun j i => X i * c j * pderiv i (u j))]
    _ = _ := by
      simp only [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

#print axioms syzygy_functional
#print axioms euler_syzygy_identity
#print axioms variable_syzygy
end NakaiVariableSyzygy
