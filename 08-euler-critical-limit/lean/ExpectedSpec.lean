import CriticalLimit

open Filter Topology
open scoped BigOperators

/-- Independent exported-statement fixture. The weights, harmonic coefficient,
finite sums, critical parameter and limit series are spelled out directly.
This checks the intended public statement against the proved theorem by unfolding
its definitions. It adds no analytic premise and uses no numerical test. -/
theorem critical_expected_spec
    (n p : ℕ → ℕ) (hn_pos : ∀ l, 1 ≤ n l)
    (hn : Tendsto n atTop atTop) (lambda0 : ℝ) (hlambda0 : 0 < lambda0)
    (hlambda : Tendsto (fun l => (n l : ℝ)^3 / (2 : ℝ)^(p l)) atTop (𝓝 lambda0)) :
    Tendsto
      (fun l =>
        (∑ k ∈ Finset.range (n l + 1),
          (((Nat.choose (n l) k : ℝ)^2 * (Nat.choose (n l + k) k : ℝ)^(p l)) /
            (Nat.factorial k : ℝ)) *
          (((p l : ℝ) + 3) * (harmonic k : ℝ) - 2 * (harmonic (n l - k) : ℝ) -
            (p l : ℝ) * (harmonic (n l + k) : ℝ))) /
        (∑ k ∈ Finset.range (n l + 1),
          ((Nat.choose (n l) k : ℝ)^2 * (Nat.choose (n l + k) k : ℝ)^(p l)) /
            (Nat.factorial k : ℝ)))
      atTop
      (𝓝 (3 * Real.eulerMascheroniConstant + Real.log lambda0 -
        2 * (∑' j : ℕ, (harmonic j : ℝ) * (lambda0^j / (Nat.factorial j : ℝ)^2)) /
          (∑' j : ℕ, lambda0^j / (Nat.factorial j : ℝ)^2))) := by
  simpa only [EulerScalingAnalytic.approximant, EulerScalingAnalytic.coefficient,
    EulerScalingAnalytic.weight, EulerScalingAnalytic.besselTerm] using
    (EulerScalingAnalytic.tendsto_approximant_critical n p hn_pos hn lambda0 hlambda0 hlambda)

#print axioms critical_expected_spec
