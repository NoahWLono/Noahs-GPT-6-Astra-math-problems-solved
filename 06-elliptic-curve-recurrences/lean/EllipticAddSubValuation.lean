import EllipticAddSubAllPoints

/-! Exact normalized valuation bounds for the symmetric-square map, using
Mathlib's discriminant Bézout identity and valuations trivial on constants. -/
namespace Astra01.EllipticAddSub
noncomputable section
set_option maxHeartbeats 2000000
open WeierstrassCurve.Affine MvPolynomial
variable {k K : Type*} [Field k] [Field K]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic] (φ : k →+* K)
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem eval₂_le_one {σ : Type*} (hφ : ∀ c : k, v (φ c) ≤ 1)
    (z : σ → K) (hz : ∀ i, v (z i) ≤ 1) (p : MvPolynomial σ k) :
    v (p.eval₂ φ z) ≤ 1 := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hφ c
  | add p q hp hq => simpa only [eval₂_add] using v.map_add_le hp hq
  | mul_X p i hp =>
    simp only [eval₂_mul, eval₂_X, map_mul]
    exact mul_le_one₀ hp zero_le (hz i)

theorem map_addSubMap (i : Fin 3) :
    (W.map φ).addSubMap i = MvPolynomial.map φ (W.addSubMap i) := by
  fin_cases i <;> simp [WeierstrassCurve.addSubMap, map_ofNat]

theorem map_addSubMapCoeff (i j : Fin 3) :
    (W.map φ).addSubMapCoeff (i,j) = MvPolynomial.map φ (W.addSubMapCoeff (i,j)) := by
  fin_cases i <;> fin_cases j <;> simp [WeierstrassCurve.addSubMapCoeff, map_ofNat]

theorem normalized_mapVector (hφ : ∀ c : k, v (φ c) ≤ 1)
    (z : Fin 3 → K) (hz : ∀ i, v (z i) ≤ 1) (hunit : ∃ i, v (z i) = 1) :
    (∀ i, v (mapVector (W.map φ) z i) ≤ 1) ∧
      ∃ i, v (mapVector (W.map φ) z i) = 1 := by
  have hle (i : Fin 3) : v (mapVector (W.map φ) z i) ≤ 1 := by
    unfold mapVector
    rw [map_addSubMap, ← eval₂_eq_eval_map]
    exact eval₂_le_one φ v hφ z hz _
  refine ⟨hle, ?_⟩
  by_contra hn
  push_neg at hn
  have hlt (i : Fin 3) : v (mapVector (W.map φ) z i) < 1 := lt_of_le_of_ne (hle i) (hn i)
  obtain ⟨i,hi⟩ := hunit
  have hb := (W.map φ).addSubMapCoeff_condition z i
  have hs : v (∑ j : Fin 3,
      (C (↑(W.map φ).Δ'⁻¹ : K) * (W.map φ).addSubMapCoeff (i,j)).eval z *
        ((W.map φ).addSubMap j).eval z) < 1 := by
    apply v.map_sum_lt one_ne_zero
    intro j _
    have hc : v ((C (↑(W.map φ).Δ'⁻¹ : K) * (W.map φ).addSubMapCoeff (i,j)).eval z) ≤ 1 := by
      rw [eval_mul, eval_C, map_mul, WeierstrassCurve.coe_inv_map_Δ', map_addSubMapCoeff,
        ← eval₂_eq_eval_map]
      exact mul_le_one₀ (hφ _) zero_le (eval₂_le_one φ v hφ z hz _)
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc zero_le (hlt j)
  rw [hb, map_pow, hi, one_pow] at hs
  exact (lt_irrefl (1 : Γ)) hs
end
end Astra01.EllipticAddSub
#print axioms Astra01.EllipticAddSub.normalized_mapVector
