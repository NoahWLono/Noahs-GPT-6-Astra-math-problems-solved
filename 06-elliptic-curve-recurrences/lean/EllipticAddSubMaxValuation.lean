import EllipticAddSubValuation

/-! Exact quadratic scaling of the largest coordinate valuation. -/
namespace Astra01.EllipticAddSub
noncomputable section
open WeierstrassCurve.Affine
variable {k K : Type*} [Field k] [Field K]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic] (φ : k →+* K)
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem mapVector_smul (a : k) (z : Fin 3 → k) :
    mapVector W (a • z) = a^2 • mapVector W z := by
  ext i
  fin_cases i <;> simp [mapVector, WeierstrassCurve.addSubMap, Pi.smul_apply, smul_eq_mul] <;> ring

/-- If a nonzero coordinate has the largest valuation, its square is exactly
the largest valuation after the actual quadratic map. -/
theorem mapVector_maximum (hφ : ∀ c : k, v (φ c) ≤ 1)
    (z : Fin 3 → K) (a : K) (ha : a ≠ 0)
    (hz : ∀ i, v (z i) ≤ v a) (he : ∃ i, v (z i) = v a) :
    (∀ i, v (mapVector (W.map φ) z i) ≤ (v a)^2) ∧
      ∃ i, v (mapVector (W.map φ) z i) = (v a)^2 := by
  let q : Fin 3 → K := fun i => z i / a
  have hapos : 0 < v a := v.pos_iff.mpr ha
  have hq (i : Fin 3) : v (q i) ≤ 1 := by
    change v (z i / a) ≤ 1
    rw [map_div₀]
    exact (div_le_one₀ hapos).mpr (hz i)
  have heq : ∃ i, v (q i) = 1 := by
    obtain ⟨i,hi⟩ := he
    refine ⟨i,?_⟩
    change v (z i / a) = 1
    rw [map_div₀,hi,div_self (ne_of_gt hapos)]
  obtain ⟨hqle,hqeq⟩ := normalized_mapVector W φ v hφ q hq heq
  have hzq : z = a • q := by
    ext i
    simp only [q, Pi.smul_apply, smul_eq_mul]
    field_simp [ha]
    <;> ring
  have hm : mapVector (W.map φ) z = a^2 • mapVector (W.map φ) q := by
    rw [hzq, mapVector_smul]
  have hv (i : Fin 3) : v (mapVector (W.map φ) z i) =
      (v a)^2 * v (mapVector (W.map φ) q i) := by
    rw [hm]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
  constructor
  · intro i
    rw [hv]
    simpa using mul_le_mul_left' (hqle i) ((v a)^2)
  · obtain ⟨i,hi⟩ := hqeq
    exact ⟨i, by rw [hv,hi,mul_one]⟩
end
end Astra01.EllipticAddSub
#print axioms Astra01.EllipticAddSub.mapVector_maximum
