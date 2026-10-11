import EllipticChordExpansion
import ValuationResidueArithmetic

namespace Astra01.EllipticAddSub
noncomputable section
variable {K : Type*} [Field K]
variable (v : Valuation K (WithZero (Multiplicative ℤ)))

private theorem mul_exp_bound {a b : K} {m n : ℤ}
    (ha : v a ≤ WithZero.exp m) (hb : v b ≤ WithZero.exp n) :
    v (a*b) ≤ WithZero.exp (m+n) := by
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' ha hb

private theorem two_le_one : v (2 : K) ≤ 1 := by
  simpa only [one_add_one_eq_two, map_one, max_self] using v.map_add 1 1

/-- The unique dominant monomial in the actual chord numerator has pole weight 4q+2. -/
theorem chordNumerator_valuation (W : WeierstrassCurve.Affine K)
    (hc : v W.a₁ ≤ 1 ∧ v W.a₂ ≤ 1 ∧ v W.a₃ ≤ 1 ∧ v W.a₄ ≤ 1 ∧ v W.a₆ ≤ 1)
    (q : ℤ) (hq : 2 ≤ q) {x u y z : K}
    (hy : W.Equation x y) (hz : W.Equation u z)
    (vx : v x = WithZero.exp 2) (vu : v u = WithZero.exp (2*q))
    (vy : v y = WithZero.exp 3) (vz : v z = WithZero.exp (3*q)) :
    v (chordNumerator W x u y z) = WithZero.exp (4*q+2) := by
  rw [chordNumerator_expansion W hy hz]
  have hm : v (x*u^2) = WithZero.exp (4*q+2) := by
    rw [map_mul, map_pow, vx, vu, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have hx2 : v (x^2) = WithZero.exp 4 := by
    rw [map_pow, vx, ← WithZero.exp_nsmul]
    rfl
  have hxu := mul_exp_bound v vx.le vu.le
  have hxy := mul_exp_bound v vx.le vz.le
  have huy := mul_exp_bound v vu.le vy.le
  have hyz := mul_exp_bound v vy.le vz.le
  have hsmall (a b : ℤ) (h : a < b) : WithZero.exp a < WithZero.exp b :=
    WithZero.exp_lt_exp.mpr h
  have hzero (a : K) (h : v a ≤ 1) : v a ≤ WithZero.exp 0 := by simpa using h
  have ha : v (x^2*u) < WithZero.exp (4*q+2) :=
    (mul_exp_bound v hx2.le vu.le).trans_lt (hsmall _ _ (by omega))
  have hb : v (2*W.a₂*x*u) < WithZero.exp (4*q+2) := by
    have h := mul_exp_bound v (mul_exp_bound v (mul_exp_bound v
      (hzero 2 (two_le_one v)) (hzero _ hc.2.1)) vx.le) vu.le
    exact h.trans_lt (hsmall _ _ (by omega))
  have hsumxu : v (x+u) ≤ WithZero.exp (2*q) :=
    v.map_add_le (vx.le.trans (WithZero.exp_le_exp.mpr (by omega))) vu.le
  have hd : v (W.a₄*(x+u)) < WithZero.exp (4*q+2) :=
    (mul_exp_bound v (hzero _ hc.2.2.2.1) hsumxu).trans_lt (hsmall _ _ (by omega))
  have he : v (2*W.a₆) < WithZero.exp (4*q+2) :=
    (mul_exp_bound v (hzero 2 (two_le_one v)) (hzero _ hc.2.2.2.2)).trans_lt
      (hsmall _ _ (by omega))
  have hf : v (2*y*z) < WithZero.exp (4*q+2) := by
    have h := mul_exp_bound v (mul_exp_bound v (hzero 2 (two_le_one v)) vy.le) vz.le
    exact h.trans_lt (hsmall _ _ (by omega))
  have hg : v (W.a₁*(x*z+u*y)) < WithZero.exp (4*q+2) := by
    have hsum := v.map_add_le hxy (huy.trans (WithZero.exp_le_exp.mpr (by omega)))
    exact (mul_exp_bound v (hzero _ hc.1) hsum).trans_lt (hsmall _ _ (by omega))
  have hh : v (W.a₃*(y+z)) < WithZero.exp (4*q+2) := by
    have hsum := v.map_add_le (vy.le.trans (WithZero.exp_le_exp.mpr (by omega))) vz.le
    exact (mul_exp_bound v (hzero _ hc.2.2.1) hsum).trans_lt (hsmall _ _ (by omega))
  have hadd {a b : K} (ha : v a = WithZero.exp (4*q+2))
      (hb : v b < WithZero.exp (4*q+2)) : v (a+b) = WithZero.exp (4*q+2) := by
    rw [v.map_add_eq_of_lt_left (by rwa [ha]), ha]
  have hsub {a b : K} (ha : v a = WithZero.exp (4*q+2))
      (hb : v b < WithZero.exp (4*q+2)) : v (a-b) = WithZero.exp (4*q+2) := by
    rw [v.map_sub_eq_of_lt_left (by rwa [ha]), ha]
  exact hsub (hsub (hsub (hadd (hadd (hadd (hadd hm ha) hb) hd) he) hf) hg) hh

end
end Astra01.EllipticAddSub
#print axioms Astra01.EllipticAddSub.chordNumerator_valuation
