import CorrectionLimit
import BaselineLimit
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field

open Filter Topology
open scoped BigOperators
noncomputable section
namespace EulerScalingAnalytic

/-- The original harmonic coefficient, with the same integer iteration parameter as `weight`. -/
def coefficient (n p k : ℕ) : ℝ :=
  ((p : ℝ) + 3) * (harmonic k : ℝ) - 2 * (harmonic (n - k) : ℝ) -
    (p : ℝ) * (harmonic (n + k) : ℝ)

/-- The original forward-indexed finite weighted approximant. -/
def approximant (n p : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), weight n p k * coefficient n p k) /
    (∑ k ∈ Finset.range (n + 1), weight n p k)

def normalizedNumerator (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), endpoint n p j * coefficient n p (n - j)

lemma coefficient_decomposition (n p j : ℕ) (hj : j ≤ n) :
    coefficient n p (n - j) = baseline n p - 2 * (harmonic j : ℝ) + correction n p j := by
  have hsub : n - (n - j) = j := by omega
  have hadd : n + (n - j) = 2 * n - j := by omega
  unfold coefficient baseline correction
  rw [hsub, hadd]
  ring

lemma normalizedDenominator_eq_forward (n p : ℕ) :
    normalizedDenominator n p =
      (∑ k ∈ Finset.range (n + 1), weight n p k) / weight n p n := by
  unfold normalizedDenominator
  rw [← Finset.sum_div]
  congr 1
  simpa using Finset.sum_range_reflect (weight n p) (n + 1)

lemma normalizedNumerator_eq_forward (n p : ℕ) :
    normalizedNumerator n p =
      (∑ k ∈ Finset.range (n + 1), weight n p k * coefficient n p k) / weight n p n := by
  rw [← Finset.sum_range_reflect (fun k => weight n p k * coefficient n p k) (n + 1)]
  simp only [Nat.add_sub_cancel, Finset.sum_div]
  unfold normalizedNumerator
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [endpoint, if_pos hjn]
  ring

lemma approximant_eq_normalized (n p : ℕ) :
    approximant n p = normalizedNumerator n p / normalizedDenominator n p := by
  rw [normalizedNumerator_eq_forward, normalizedDenominator_eq_forward]
  exact (div_div_div_cancel_right₀ (ne_of_gt (weight_endpoint_pos n p)) _ _).symm

lemma normalizedDenominator_eq_sum_endpoint (n p : ℕ) :
    normalizedDenominator n p = ∑ j ∈ Finset.range (n + 1), endpoint n p j := by
  unfold normalizedDenominator
  apply Finset.sum_congr rfl
  intro j hj
  simp [endpoint, Nat.le_of_lt_succ (Finset.mem_range.mp hj)]

lemma harmonic_endpoint_tsum_eq_sum (n p : ℕ) :
    (∑' j, (harmonic j : ℝ) * endpoint n p j) =
      ∑ j ∈ Finset.range (n + 1), (harmonic j : ℝ) * endpoint n p j := by
  apply tsum_eq_sum
  intro j hj
  have hjn : ¬ j ≤ n := by simpa using hj
  simp [endpoint, hjn]

lemma weightedCorrection_tsum_eq_sum (n p : ℕ) :
    (∑' j, weightedCorrection n p j) =
      ∑ j ∈ Finset.range (n + 1), weightedCorrection n p j := by
  apply tsum_eq_sum
  intro j hj
  have hjn : ¬ j ≤ n := by simpa using hj
  simp [weightedCorrection, endpoint, hjn]

lemma normalizedNumerator_decomposition (n p : ℕ) :
    normalizedNumerator n p = baseline n p * normalizedDenominator n p -
      2 * (∑' j, (harmonic j : ℝ) * endpoint n p j) +
      ∑' j, weightedCorrection n p j := by
  rw [normalizedDenominator_eq_sum_endpoint, harmonic_endpoint_tsum_eq_sum,
    weightedCorrection_tsum_eq_sum]
  unfold normalizedNumerator
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficient_decomposition n p j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  unfold weightedCorrection
  ring

lemma besselSeries_pos {x : ℝ} (hx : 0 ≤ x) : 0 < ∑' j, besselTerm x j := by
  apply (summable_besselTerm hx).tsum_pos (besselTerm_nonneg hx) 0
  norm_num [besselTerm]

/-- Critical scaling of the original finite approximant, in series form.
Only the integer-pair scaling assumptions are hypotheses. All analytic dependencies
are proved in the imported sources. No Bessel identity is used. -/
theorem tendsto_approximant_critical
    (n p : ℕ → ℕ) (hn_pos : ∀ l, 1 ≤ n l)
    (hn : Tendsto n atTop atTop) (lambda0 : ℝ) (hlambda0 : 0 < lambda0)
    (hlambda : Tendsto (fun l => scale (n l) (p l)) atTop (𝓝 lambda0)) :
    Tendsto (fun l => approximant (n l) (p l)) atTop
      (𝓝 (3 * Real.eulerMascheroniConstant + Real.log lambda0 -
        2 * (∑' j, (harmonic j : ℝ) * besselTerm lambda0 j) /
          (∑' j, besselTerm lambda0 j))) := by
  have hD := tendsto_normalizedDenominator n p hn_pos hn lambda0 hlambda0 hlambda
  have hC := tendsto_baseline n p hn_pos hn lambda0 hlambda0 hlambda
  have hH := tendsto_harmonic_endpoint_tsum n p hn_pos hn lambda0 hlambda0 hlambda
  have hE := tendsto_weightedCorrection_tsum n p hn_pos hn lambda0 hlambda0 hlambda
  have hN : Tendsto (fun l => normalizedNumerator (n l) (p l)) atTop
      (𝓝 ((3 * Real.eulerMascheroniConstant + Real.log lambda0) *
        (∑' j, besselTerm lambda0 j) -
        2 * (∑' j, (harmonic j : ℝ) * besselTerm lambda0 j))) := by
    have h := ((hC.mul hD).sub (hH.const_mul 2)).add hE
    simp only [add_zero] at h
    apply h.congr'
    exact Filter.Eventually.of_forall (fun l => (normalizedNumerator_decomposition (n l) (p l)).symm)
  have hne := ne_of_gt (besselSeries_pos (le_of_lt hlambda0))
  have h := hN.div hD hne
  have halg :
      ((3 * Real.eulerMascheroniConstant + Real.log lambda0) *
        (∑' j, besselTerm lambda0 j) -
        2 * (∑' j, (harmonic j : ℝ) * besselTerm lambda0 j)) /
        (∑' j, besselTerm lambda0 j) =
      3 * Real.eulerMascheroniConstant + Real.log lambda0 -
        2 * (∑' j, (harmonic j : ℝ) * besselTerm lambda0 j) /
          (∑' j, besselTerm lambda0 j) := by field_simp
  rw [halg] at h
  exact h.congr' (Filter.Eventually.of_forall
    (fun l => (approximant_eq_normalized (n l) (p l)).symm))

#print axioms tendsto_approximant_critical
end EulerScalingAnalytic
