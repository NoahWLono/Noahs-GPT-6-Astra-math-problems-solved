import NakaiHomogeneousCoefficients
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! Pure-power membership from finite-dimensional homogeneous quotients. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NakaiFiniteQuotient
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev P := MvPolynomial ι k
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The top homogeneous component of a monic univariate polynomial evaluated
at a variable is the corresponding pure power. -/
theorem top_component_monic_aeval (p : Polynomial k) (hp : p.Monic) (i : ι) :
    homogeneousComponent p.natDegree (Polynomial.aeval (X i : P (k := k) (ι := ι)) p) =
      (X i)^p.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  simp only [Algebra.smul_def, algebraMap_eq, map_sum]
  simp_rw [homogeneousComponent_of_mem (isHomogeneous_C_mul_X_pow _ i _)]
  simp only [Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_self, if_true,
    hp.coeff_natDegree, map_one, one_mul]

/-- A finite homogeneous quotient forces a power of each variable into its ideal. -/
theorem exists_variable_power (J : Ideal (P (k := k) (ι := ι)))
    (hJ : J.IsHomogeneous (homogeneousSubmodule ι k))
    [Module.Finite k (P (k := k) (ι := ι) ⧸ J)] (i : ι) :
    ∃ N : ℕ, (X i : P (k := k) (ι := ι))^N ∈ J := by
  obtain ⟨p, hp, hz⟩ := IsIntegral.of_finite k (Ideal.Quotient.mk J (X i))
  have hmem : Polynomial.aeval (X i : P (k := k) (ι := ι)) p ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have ha := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k J) (X i) p
    simp only [Ideal.Quotient.mkₐ_eq_mk] at ha
    rw [← ha]
    simpa only [Polynomial.aeval_def] using hz
  refine ⟨p.natDegree, ?_⟩
  have ht := homogeneousComponent_mem_of_mem hJ hmem p.natDegree
  rwa [top_component_monic_aeval p hp i] at ht

/-- Individual power witnesses can be enlarged to a common positive exponent
above any prescribed degree. -/
theorem common_variable_powers (J : Ideal (P (k := k) (ι := ι))) (r : ℕ)
    (hp : ∀ i : ι, ∃ n : ℕ, (X i : P (k := k) (ι := ι))^n ∈ J) :
    ∃ N : ℕ, 0 < N ∧ r ≤ N ∧ ∀ i : ι, (X i : P (k := k) (ι := ι))^N ∈ J := by
  choose n hn using hp
  let N := r+1+∑ i, n i
  have hr : r < N := by
    exact lt_of_lt_of_le (Nat.lt_succ_self r) (Nat.le_add_right _ _)
  refine ⟨N, lt_of_le_of_lt (Nat.zero_le r) hr, Nat.le_of_lt hr, ?_⟩
  intro i
  have hni : n i ≤ N := by
    exact le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i))
      (Nat.le_add_left _ _)
  have hh := Ideal.mul_mem_left J ((X i : P (k := k) (ι := ι))^(N-n i)) (hn i)
  rwa [← pow_add, Nat.sub_add_cancel hni] at hh

#print axioms top_component_monic_aeval
#print axioms exists_variable_power
#print axioms common_variable_powers
end NakaiFiniteQuotient
