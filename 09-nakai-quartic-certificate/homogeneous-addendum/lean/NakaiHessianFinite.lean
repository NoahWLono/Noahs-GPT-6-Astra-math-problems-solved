import NakaiPurePowers
import NakaiFiniteQuotient
import NakaiHomogeneousEuler

/-! Hessian nonmembership for homogeneous polynomials with finite gradient quotient,
proved by homogeneous determinant comparison and pure powers. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NakaiHomogeneous
open NakaiFramework NakaiDeterminantRow
variable {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem gradientIdeal_isHomogeneous (f : P (k := k) (ι := ι)) (d : ℕ)
    (hf : f.IsHomogeneous d) :
    (gradientIdeal f).IsHomogeneous (homogeneousSubmodule ι k) := by
  apply Ideal.homogeneous_span (homogeneousSubmodule ι k)
  rintro p ⟨i, rfl⟩
  exact ⟨d-1, hf.pderiv⟩

/-- The Hessian class is nonzero in a finite-dimensional homogeneous gradient
quotient. No socle or nonmembership result is an input hypothesis. -/
theorem hessian_not_mem_of_finite (f : P (k := k) (ι := ι)) (d : ℕ)
    (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    [Module.Finite k (P (k := k) (ι := ι) ⧸ gradientIdeal f)] :
    h f ∉ gradientIdeal f := by
  have hd1 : 1 ≤ d := le_trans (by decide : 1 ≤ 2) hd
  have hr1 : 1 ≤ d-1 := Nat.le_sub_of_add_le hd
  have hr0 : ((d-1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hr1)
  let c : k := ((d-1 : ℕ) : k)⁻¹
  let A : Matrix ι ι (P (k := k) (ι := ι)) := (C c : P (k := k) (ι := ι)) • H f
  have hcast : C ((d-1 : ℕ) : k) = (d : P (k := k) (ι := ι))-1 := by
    rw [map_natCast, Nat.cast_sub hd1, Nat.cast_one]
  have hArow : rowValue A X = fun i => pderiv i f := by
    funext i
    simp only [rowValue, A, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [H_mul_X f d hf hd, ← hcast, ← mul_assoc, ← map_mul]
    simp only [c, inv_mul_cancel₀ hr0, map_one, one_mul]
  have hA : ∀ i j, (A i j).IsHomogeneous ((d-1)-1) := by
    intro i j
    exact ((hf.pderiv (i := j)).pderiv (i := i)).C_mul c
  obtain ⟨N, hN, hrN, hpowers⟩ := NakaiFiniteQuotient.common_variable_powers
    (gradientIdeal f) (d-1)
    (NakaiFiniteQuotient.exists_variable_power (gradientIdeal f) (gradientIdeal_isHomogeneous f d hf))
  obtain ⟨B, hB, hBg⟩ := NakaiHomogeneousCoefficients.homogeneous_pure_power_coefficients
    (fun i => pderiv i f) (d-1) N (fun i => hf.pderiv) hrN hpowers
  have hdeg : (N-(d-1))+((d-1)-1) = N-1 := by
    rw [← Nat.add_sub_assoc hr1, Nat.sub_add_cancel hrN]
  have hBA : ∀ i j, ((B*A) i j).IsHomogeneous (N-1) := by
    intro i j
    rw [Matrix.mul_apply, ← hdeg]
    exact IsHomogeneous.sum _ _ _ (fun l _ => (hB i l).mul (hA l j))
  have hdet := NakaiPurePowers.determinant_not_mem_span A B N hN hBA (by
    intro i
    rw [hArow]
    exact hBg i)
  rw [hArow] at hdet
  intro hh
  apply hdet
  change ((C c : P (k := k) (ι := ι)) • H f).det ∈ gradientIdeal f
  rw [Matrix.det_smul]
  exact Ideal.mul_mem_left _ _ hh

#print axioms gradientIdeal_isHomogeneous
#print axioms hessian_not_mem_of_finite
end NakaiHomogeneous
