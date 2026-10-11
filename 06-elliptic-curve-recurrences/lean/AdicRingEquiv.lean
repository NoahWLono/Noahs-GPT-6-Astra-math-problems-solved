import FunctionFieldPlaces

/-! Normalized adic valuations are preserved under compatible ring
isomorphisms between two Dedekind models of the same fraction field. -/
namespace Astra01
noncomputable section
open IsDedekindDomain
open scoped nonZeroDivisors
variable {R S K : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Field K]
  [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsFractionRing S K]

theorem intValuation_ringEquiv (e : R ≃+* S) (v : HeightOneSpectrum R) (r : R) :
    (HeightOneSpectrum.equivOfRingEquiv e v).intValuation (e r) = v.intValuation r := by
  classical
  let w := HeightOneSpectrum.equivOfRingEquiv e v
  have ht (n : ℕ) : w.intValuation (e r) ≤ WithZero.exp (-(n : ℤ)) ↔
      v.intValuation r ≤ WithZero.exp (-(n : ℤ)) := by
    rw [w.intValuation_le_pow_iff_mem, v.intValuation_le_pow_iff_mem]
    change e r ∈ (v.asIdeal.comap e.symm)^n ↔ r ∈ v.asIdeal^n
    rw [← Ideal.map_comap_of_equiv e, ← Ideal.map_pow]
    exact Ideal.apply_mem_of_equiv_iff
  by_cases hr : r = 0
  · simp [hr]
  · have her : e r ≠ 0 := by simpa using e.injective.ne hr
    have hv := v.intValuation_if_neg hr
    have hw := w.intValuation_if_neg her
    have ht' := ht
    simp only [hw, hv, WithZero.exp_le_exp, neg_le_neg_iff, Int.ofNat_le] at ht'
    have hn := Nat.le_antisymm ((ht' _).mp le_rfl) ((ht' _).mpr le_rfl)
    change w.intValuation (e r) = v.intValuation r
    rw [hw, hv, hn]

theorem valuation_ringEquiv (e : R ≃+* S)
    (he : ∀ r : R, algebraMap S K (e r) = algebraMap R K r)
    (v : HeightOneSpectrum R) :
    (HeightOneSpectrum.equivOfRingEquiv e v).valuation K = v.valuation K := by
  let w := HeightOneSpectrum.equivOfRingEquiv e v
  have hval (r : R) : w.valuation K (algebraMap R K r) = v.valuation K (algebraMap R K r) := by
    calc
      _ = w.valuation K (algebraMap S K (e r)) := congrArg (w.valuation K) (he r).symm
      _ = w.intValuation (e r) := w.valuation_of_algebraMap (K := K) _
      _ = v.intValuation r := intValuation_ringEquiv e v r
      _ = v.valuation K (algebraMap R K r) := (v.valuation_of_algebraMap (K := K) _).symm
  ext x
  obtain ⟨a,b,h⟩ := IsLocalization.exists_mk'_eq R⁰ x
  rw [← h, IsFractionRing.mk'_eq_div]
  change w.valuation K (_ / _) = v.valuation K (_ / _)
  rw [map_div₀, map_div₀, hval, hval]
end
end Astra01
#print axioms Astra01.valuation_ringEquiv
