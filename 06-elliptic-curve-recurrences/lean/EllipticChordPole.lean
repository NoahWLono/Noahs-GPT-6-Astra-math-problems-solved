import EllipticChordValuation
import EllipticAddSubCompatibility

namespace Astra01.EllipticAddSub
noncomputable section
variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq _
variable (v : Valuation K (WithZero (Multiplicative ℤ)))

theorem addX_valuation (W : WeierstrassCurve.Affine K)
    (hc : v W.a₁ ≤ 1 ∧ v W.a₂ ≤ 1 ∧ v W.a₃ ≤ 1 ∧ v W.a₄ ≤ 1 ∧ v W.a₆ ≤ 1)
    (q : ℤ) (hq : 2 ≤ q) {x u y z : K}
    (hy : W.Equation x y) (hz : W.Equation u z)
    (vx : v x = WithZero.exp 2) (vu : v u = WithZero.exp (2*q))
    (vy : v y = WithZero.exp 3) (vz : v z = WithZero.exp (3*q)) :
    v (W.addX x u (W.slope x u y z)) = WithZero.exp 2 := by
  have hxu : x ≠ u := by
    intro h
    have h' := congrArg v h
    rw [vx,vu] at h'
    have := WithZero.exp_injective h'
    omega
  have hden : v (u-x) = WithZero.exp (2*q) := by
    rw [v.map_sub_eq_of_lt_left (by rw [vx,vu]; exact WithZero.exp_lt_exp.mpr (by omega)),vu]
  rw [addX_chord W y z hxu, Valuation.map_div,
    chordNumerator_valuation v W hc q hq hy hz vx vu vy vz, map_pow, hden,
    ← WithZero.exp_nsmul, ← WithZero.exp_sub]
  congr 1
  simp only [nsmul_eq_mul]
  ring

theorem negY_valuation (W : WeierstrassCurve.Affine K)
    (ha : v W.a₁ ≤ 1) (hb : v W.a₃ ≤ 1) (q : ℤ) (hq : 1 ≤ q)
    {x y : K} (hx : v x = WithZero.exp (2*q)) (hy : v y = WithZero.exp (3*q)) :
    v (W.negY x y) = WithZero.exp (3*q) := by
  have hax : v (W.a₁*x) ≤ WithZero.exp (2*q) := by
    rw [map_mul,hx]
    simpa using mul_le_mul_right' ha (WithZero.exp (2*q))
  have hsmall : v (W.a₁*x) < v (-y) := by
    rw [Valuation.map_neg,hy]
    exact hax.trans_lt (WithZero.exp_lt_exp.mpr (by omega))
  have hmain : v (-y-W.a₁*x) = WithZero.exp (3*q) := by
    rw [v.map_sub_eq_of_lt_left hsmall,Valuation.map_neg,hy]
  unfold WeierstrassCurve.Affine.negY
  rw [v.map_sub_eq_of_lt_left (by
    rw [hmain]
    exact hb.trans_lt (by simpa only [← WithZero.exp_zero] using
      WithZero.exp_lt_exp.mpr (show (0 : ℤ) < 3*q by omega))),hmain]

end
end Astra01.EllipticAddSub
#print axioms Astra01.EllipticAddSub.addX_valuation

#print axioms Astra01.EllipticAddSub.negY_valuation
