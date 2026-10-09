import QuadraticFourWeights

namespace BooleanANF.QuadraticFour

theorem cost_add_one (q : V → F₂) : cost (fun x => q x + 1) = 14 - cost q := by
  have hw := weight_add q (fun _ : V => (1 : F₂))
  have hw1 : weight (fun _ : V => (1 : F₂)) = 16 := by decide
  simp only [hw1, mul_one] at hw
  have hb : (((q 0 + 1).val : ℕ) : ℤ) = 1 - ((q 0).val : ℤ) := by
    generalize q 0 = a
    fin_cases a <;> decide
  unfold cost
  rw [hw, hb]
  ring

/-- Two rows with constant sum are equal or complementary; their costs are
equal or sum to fourteen. This cheaply excludes the exceptional d=1 partitions. -/
theorem constant_sum_costs (p q : V → F₂)
    (hc : ∀ x, p x + q x = p 0 + q 0) :
    cost p = cost q ∨ cost p + cost q = 14 := by
  have he (x : V) : q x = p x + (p 0 + q 0) := by
    calc
      q x = (p x + p x) + q x := by rw [CharTwo.add_self_eq_zero, zero_add]
      _ = p x + (p x + q x) := by rw [add_assoc]
      _ = p x + (p 0 + q 0) := by rw [hc]
  have hbit : p 0 + q 0 = 0 ∨ p 0 + q 0 = 1 := by
    generalize p 0 + q 0 = a
    fin_cases a <;> simp
  rcases hbit with h | h
  · left
    have hfun : q = p := by funext x; simpa [h] using he x
    rw [hfun]
  · right
    have hfun : q = fun x => p x + 1 := by funext x; simpa [h] using he x
    rw [hfun, cost_add_one]
    omega

#print axioms constant_sum_costs
end BooleanANF.QuadraticFour
