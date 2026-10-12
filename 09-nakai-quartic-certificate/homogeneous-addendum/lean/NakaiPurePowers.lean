import NakaiHomogeneousDeterminant
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! A pure-power determinant nonmembership certificate. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace NakaiPurePowers
open NakaiDeterminantRow NakaiHomogeneousDeterminant
variable {k ι : Type*} [Field k] [CharZero k] [Fintype ι] [DecidableEq ι]
abbrev P := MvPolynomial ι k

def powerIdeal (N : ℕ) : Ideal (P (k := k) (ι := ι)) :=
  Ideal.span (Set.range (fun i : ι => (X i : P (k := k) (ι := ι)) ^ N))

def topMonomial (N : ℕ) : P (k := k) (ι := ι) := ∏ i : ι, X i ^ (N-1)

/-- The monomial immediately below the pure powers does not belong to their ideal. -/
theorem topMonomial_not_mem (N : ℕ) (hN : 0 < N) :
    topMonomial (k := k) (ι := ι) N ∉ powerIdeal N := by
  intro hh
  have hset : Set.range (fun i : ι => (X i : P (k := k) (ι := ι)) ^ N) =
      (fun d : ι →₀ ℕ => monomial d (1 : k)) '' Set.range (fun i : ι => Finsupp.single i N) := by
    rw [← Set.range_comp]
    simp only [Function.comp_def, X_pow_eq_monomial]
  rw [powerIdeal, hset] at hh
  let t : ι →₀ ℕ := Finsupp.indicator Finset.univ (fun _ _ => N-1)
  have ht : topMonomial (k := k) (ι := ι) N = monomial t (1 : k) := by
    exact prod_X_pow (fun _ : ι => N-1) Finset.univ
  rw [ht] at hh
  have hsupport : t ∈ (monomial t (1 : k) : P (k := k) (ι := ι)).support := by simp
  obtain ⟨s, ⟨i, rfl⟩, hle⟩ := mem_ideal_span_monomial_image.mp hh t hsupport
  have hineq := hle i
  have heval : t i = N-1 := by simp [t]
  rw [Finsupp.single_eq_same, heval] at hineq
  exact (Nat.not_le.mpr (Nat.sub_lt hN (by decide))) hineq

omit [CharZero k] [DecidableEq ι] in
lemma rowValue_mul (A B : Matrix ι ι (P (k := k) (ι := ι)))
    (x : ι → P (k := k) (ι := ι)) (i : ι) :
    rowValue (B*A) x i = rowValue B (rowValue A x) i := by
  simp only [rowValue, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- An explicit homogeneous matrix certificate proves determinant nonmembership.
It assumes pure-power witnesses, not the desired determinant nonmembership. -/
theorem determinant_not_mem_span (A B : Matrix ι ι (P (k := k) (ι := ι)))
    (N : ℕ) (hN : 0 < N)
    (hBA : ∀ i j, ((B*A) i j).IsHomogeneous (N-1))
    (hpowers : ∀ i, rowValue B (rowValue A X) i = (X i)^N) :
    A.det ∉ Ideal.span (Set.range (rowValue A X)) := by
  let I : Ideal (P (k := k) (ι := ι)) := powerIdeal N
  let D : Matrix ι ι (P (k := k) (ι := ι)) := Matrix.diagonal (fun i => X i^(N-1))
  have hD : ∀ i j, (D i j).IsHomogeneous (N-1) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [D] using (isHomogeneous_X k i).pow (N-1)
    · simpa [D, Matrix.diagonal_apply, hij] using isHomogeneous_zero (R := k) (σ := ι) (N-1)
  have hDrow : ∀ i, rowValue D X i = (X i)^N := by
    intro i
    simp only [rowValue, D, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← pow_succ]
    congr 1
    exact Nat.sub_add_cancel hN
  have hCmem : ∀ i, rowValue (B*A) X i ∈ I := by
    intro i
    rw [rowValue_mul, hpowers]
    exact Ideal.subset_span (Set.mem_range_self i)
  have hdiff := determinant_comparison (B*A) D (N-1) hBA hD
    (fun i => by rw [rowValue_mul, hpowers, hDrow]) I hCmem
  have hdetD : D.det = topMonomial (k := k) (ι := ι) N := Matrix.det_diagonal
  rw [Matrix.det_mul, hdetD] at hdiff
  have hgen : ∀ i, B.det * rowValue A X i ∈ I := by
    intro i
    rw [← adjugate_rows B (rowValue A X) i]
    apply Submodule.sum_mem
    intro j _
    rw [hpowers]
    exact Ideal.mul_mem_left I _ (Ideal.subset_span (Set.mem_range_self j))
  intro hA
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hA
  have hprod : B.det * A.det ∈ I := by
    rw [← hc, Finset.mul_sum]
    apply Submodule.sum_mem
    intro i _
    simpa only [mul_left_comm] using Ideal.mul_mem_left I (c i) (hgen i)
  have htop := I.sub_mem hprod hdiff
  have htop' : topMonomial (k := k) (ι := ι) N ∈ I := by
    convert htop using 1 <;> ring
  exact topMonomial_not_mem N hN htop'

#print axioms topMonomial_not_mem
#print axioms determinant_not_mem_span
end NakaiPurePowers
