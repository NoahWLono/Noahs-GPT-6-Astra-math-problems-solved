import EndpointWeights
import ParameterDecay
import BesselSeries
import FactorLimit
import Mathlib.Analysis.Normed.Group.Tannery

open Filter Topology
open scoped BigOperators

noncomputable section

namespace EulerScalingAnalytic

/-- The original finite denominator, divided by its endpoint weight.
The index is reversed, but each summand is the original binomial/factorial weight. -/
def normalizedDenominator (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), weight n p (n - j) / weight n p n

lemma normalizedDenominator_eq_tsum (n p : ℕ) :
    normalizedDenominator n p = ∑' j, endpoint n p j := by
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun j hj => ?_)]
  · apply Finset.sum_congr rfl
    intro j hj
    have h : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simp [endpoint, h]
  · have h : ¬ j ≤ n := by simpa using hj
    simp [endpoint, h]

lemma scale_nonneg (n p : ℕ) : 0 ≤ scale n p := by
  unfold scale
  positivity

lemma endpoint_nonneg (n p j : ℕ) : 0 ≤ endpoint n p j := by
  unfold endpoint
  split_ifs with h
  · exact le_of_lt (div_pos (weight_pos n p (n - j) (Nat.sub_le n j))
      (weight_endpoint_pos n p))
  · rfl

lemma endpoint_le_besselTerm (n p j : ℕ) (hn : 1 ≤ n) :
    endpoint n p j ≤ besselTerm (scale n p) j := by
  by_cases hj : j ≤ n
  · rw [endpoint_eq_product n p j hn hj]
    change besselTerm (scale n p) j *
      (∏ r ∈ Finset.range j, endpointFactor n p r) ≤ besselTerm (scale n p) j
    have hp : (∏ r ∈ Finset.range j, endpointFactor n p r) ≤ 1 :=
      Finset.prod_le_one
        (fun r hr => endpointFactor_nonneg n p r hn ((Finset.mem_range.mp hr).trans_le hj))
        (fun r hr => endpointFactor_le_one n p r hn ((Finset.mem_range.mp hr).trans_le hj))
    exact (mul_le_mul_of_nonneg_left hp (besselTerm_nonneg (scale_nonneg n p) j)).trans_eq
      (mul_one _)
  · simp only [endpoint, if_neg hj]
    exact besselTerm_nonneg (scale_nonneg n p) j

lemma tendsto_endpoint (n p : ℕ → ℕ) (hn_pos : ∀ l, 1 ≤ n l)
    (hn : Tendsto n atTop atTop) (lambda0 : ℝ) (hlambda0 : 0 < lambda0)
    (hlambda : Tendsto (fun l => scale (n l) (p l)) atTop (𝓝 lambda0)) (j : ℕ) :
    Tendsto (fun l => endpoint (n l) (p l) j) atTop (𝓝 (besselTerm lambda0 j)) := by
  have hp : Tendsto (fun l => (p l : ℝ) / (n l : ℝ)) atTop (𝓝 0) :=
    EulerScaling.tendsto_parameter_div_scale_zero n p hn_pos hn lambda0 hlambda0 hlambda
  have hprod : Tendsto (fun l => ∏ r ∈ Finset.range j, endpointFactor (n l) (p l) r)
      atTop (𝓝 1) := by
    have h := tendsto_finsetProd (Finset.range j)
      (fun r _ => tendsto_endpointFactor n p hn_pos hn hp r)
    simpa using h
  have hlim : Tendsto (fun l => besselTerm (scale (n l) (p l)) j *
      ∏ r ∈ Finset.range j, endpointFactor (n l) (p l) r)
      atTop (𝓝 (besselTerm lambda0 j)) := by
    simpa using (tendsto_besselTerm hlambda j).mul hprod
  apply hlim.congr'
  filter_upwards [hn.eventually (eventually_ge_atTop j)] with l hl
  simpa only [besselTerm, endpointFactor] using
    (endpoint_eq_product (n l) (p l) j (hn_pos l) hl).symm

/-- Critical scaling of the normalized denominator along integer pairs.
The parameter decay, summability, pointwise limits and domination are proved
from the displayed hypotheses; no denominator limit is assumed. -/
theorem tendsto_normalizedDenominator
    (n p : ℕ → ℕ) (hn_pos : ∀ l, 1 ≤ n l)
    (hn : Tendsto n atTop atTop) (lambda0 : ℝ) (hlambda0 : 0 < lambda0)
    (hlambda : Tendsto (fun l => scale (n l) (p l)) atTop (𝓝 lambda0)) :
    Tendsto (fun l => normalizedDenominator (n l) (p l)) atTop
      (𝓝 (∑' j, besselTerm lambda0 j)) := by
  have hm : 0 ≤ lambda0 + 1 := by linarith
  have hsum := summable_besselTerm hm
  have hbound : ∀ᶠ l in atTop, ∀ j,
      ‖endpoint (n l) (p l) j‖ ≤ besselTerm (lambda0 + 1) j := by
    filter_upwards [hlambda.eventually_le_const (show lambda0 < lambda0 + 1 by linarith)]
      with l hl j
    rw [Real.norm_eq_abs, abs_of_nonneg (endpoint_nonneg (n l) (p l) j)]
    exact (endpoint_le_besselTerm (n l) (p l) j (hn_pos l)).trans
      (besselTerm_mono (scale_nonneg (n l) (p l)) hl j)
  have hlim := tendsto_tsum_of_dominated_convergence hsum
    (fun j => tendsto_endpoint n p hn_pos hn lambda0 hlambda0 hlambda j) hbound
  simpa only [normalizedDenominator_eq_tsum] using hlim

#print axioms tendsto_normalizedDenominator

end EulerScalingAnalytic
