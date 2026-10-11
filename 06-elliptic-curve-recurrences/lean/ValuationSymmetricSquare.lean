import EllipticHeightScaling

/-! The two-root Gauss-norm identity needed for symmetric-square height. -/
namespace Astra01
variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

theorem valuation_symmetric_square (v : Valuation K Γ) (x y : K) :
    max (v (x*y)) (max (v (x+y)) 1) = max (v x) 1 * max (v y) 1 := by
  rw [map_mul]
  by_cases hx : v x ≤ 1
  · by_cases hy : v y ≤ 1
    · have hs := v.map_add_le hx hy
      have hp := mul_le_one₀ hx zero_le hy
      rw [max_eq_right hs, max_eq_right hp, max_eq_right hx, max_eq_right hy, one_mul]
    · have hy' := lt_of_not_ge hy
      have hs := v.map_add_eq_of_lt_right (hx.trans_lt hy')
      have hp : v x * v y ≤ v y := by simpa using mul_le_mul_right' hx (v y)
      rw [hs, max_eq_left hy'.le, max_eq_right hp, max_eq_right hx, one_mul]
  · have hx' := lt_of_not_ge hx
    by_cases hy : v y ≤ 1
    · have hs := v.map_add_eq_of_lt_left (hy.trans_lt hx')
      have hp : v x * v y ≤ v x := by simpa using mul_le_mul_left' hy (v x)
      rw [hs, max_eq_left hx'.le, max_eq_right hp, max_eq_right hy, mul_one]
    · have hy' := lt_of_not_ge hy
      have hxp : v x ≤ v x * v y := by simpa using mul_le_mul_left' hy'.le (v x)
      have hyp : v y ≤ v x * v y := by simpa using mul_le_mul_right' hx'.le (v y)
      have hs := v.map_add_le hxp hyp
      have hp : 1 ≤ v x * v y := hx'.le.trans hxp
      rw [max_eq_left (max_le hs hp), max_eq_left hx'.le, max_eq_left hy'.le]
end Astra01
#print axioms Astra01.valuation_symmetric_square
