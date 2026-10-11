import LinearFractionProjective

/-! Faithful base extension preserves and reflects projective linear-fraction
agreement, including infinity. -/
namespace Astra01
noncomputable section
open Polynomial
open scoped Polynomial
variable {k l : Type*} [Field k] [Field l]

theorem linearFraction_baseChange_iff (φ : k →+* l) (b c d : k)
    (hc : c ≠ 0) (hd : d-b*c ≠ 0) (z w : Option k) :
    w.map φ = rationalProjectiveMap (X+C (φ b)) (C (φ c)*X+C (φ d)) (z.map φ) ↔
      w = rationalProjectiveMap (X+C b) (C c*X+C d) z := by
  have hc' : φ c ≠ 0 := fun h => hc (φ.injective (h.trans φ.map_zero.symm))
  have hd' : φ d-φ b*φ c ≠ 0 := by
    rw [← map_mul, ← map_sub]
    exact fun h => hd (φ.injective (h.trans φ.map_zero.symm))
  rw [linearFraction_projective _ _ _ hc' hd', linearFraction_projective _ _ _ hc hd]
  cases z <;> cases w <;>
    simp only [Option.map_none, Option.map_some, homogeneous, mul_zero, mul_one,
      zero_mul, one_mul, add_zero, zero_add] <;>
    simpa only [← map_mul, ← map_add, ← map_one φ, ← map_zero φ] using φ.injective.eq_iff
end
end Astra01
#print axioms Astra01.linearFraction_baseChange_iff
