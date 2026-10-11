import EllipticCompositionDegree

/-! A nonconstant elliptic function has positive pole degree. The affine
unit calculation uses the genuine quadratic norm, and the global statement
uses the checked complete place dictionary and product formula. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]

theorem coordinate_unit_constant (z : W.CoordinateRing) (hz : IsUnit z) :
    ∃ c : k, algebraMap k W.CoordinateRing c = z := by
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq z
  have hn := Polynomial.degree_eq_zero_of_isUnit (hz.map (Algebra.norm k[X]))
  rw [← hpq, CoordinateRing.degree_norm_smul_basis] at hn
  have hq : q = 0 := by
    by_contra hq
    have hle : 2 • q.degree + 3 ≤ 0 := hn ▸ le_max_right _ _
    rw [Polynomial.degree_eq_natDegree hq] at hle
    norm_cast at hle
  have hp : p ≠ 0 := by
    intro hp
    have hz0 : z = 0 := by simpa [hp, hq] using hpq.symm
    exact hz.ne_zero hz0
  have hle : 2 • p.degree ≤ 0 := hn ▸ le_max_left _ _
  rw [Polynomial.degree_eq_natDegree hp] at hle
  norm_cast at hle
  simp only [nsmul_eq_mul] at hle
  change ((2 * p.natDegree : ℕ) : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) at hle
  have hleN : 2 * p.natDegree ≤ 0 := WithBot.coe_le_coe.mp hle
  have hp0 : p.natDegree = 0 := by omega
  refine ⟨p.coeff 0, ?_⟩
  rw [← hpq, hq, zero_smul, add_zero, Polynomial.eq_C_of_natDegree_eq_zero hp0]
  simp only [Algebra.smul_def, mul_one]
  simpa using IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing (p.coeff 0)

variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : IsScalarTower k W.CoordinateRing K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing,
      ← IsScalarTower.algebraMap_apply k[X] W.CoordinateRing K]

theorem divisorDegree_eq_zero_iff (d : W.Point →₀ ℕ) : divisorDegree W d = 0 ↔ d = 0 := by
  classical
  constructor
  · intro h
    ext P
    by_cases hP : P ∈ d.support
    · exact (Finset.sum_eq_zero_iff.mp h) P hP
    · exact by simpa using hP
  · rintro rfl
    rfl

theorem principalDivisor_eq_zero_of_pole_degree_zero (f : Kˣ)
    (hf : divisorDegree W (poleDivisor W K f) = 0) :
    principalDivisor W K (Additive.ofMul f) = 0 := by
  have hp := (divisorDegree_eq_zero_iff W _).mp hf
  have hz := (divisorDegree_eq_zero_iff W _).mp ((zero_degree_eq_pole_degree W K f).trans hf)
  ext P
  have hpP := congrArg (fun d : W.Point →₀ ℕ => d P) hp
  have hzP := congrArg (fun d : W.Point →₀ ℕ => d P) hz
  simp only [zeroDivisor, poleDivisor, Finsupp.mapRange_apply, Finsupp.zero_apply] at hpP hzP ⊢
  omega


theorem constant_of_principalDivisor_zero (f : Kˣ)
    (hf : principalDivisor W K (Additive.ofMul f) = 0) :
    ∃ c : k, algebraMap k K c = (f : K) := by
  have hv : ∀ v : PlaceA k K, placeValuation k K v (f : K) = 1 := by
    intro v
    obtain ⟨P, rfl⟩ := placeOfPoint_surjective W K v
    have he := point_valuation_eq W K (Additive.ofMul f) P
    simpa [hf] using he
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := ringOfIntegers k K) K (f : K) (fun v => le_of_eq (hv (Sum.inl v)))
  obtain ⟨s, hs⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := ringOfIntegers k K) K ((f : K)⁻¹) (fun v => by
      change placeValuation k K (Sum.inl v) ((f : K)⁻¹) ≤ 1
      rw [map_inv₀, hv, inv_one])
  have hrs : r * s = 1 := by
    apply IsFractionRing.injective (ringOfIntegers k K) K
    rw [map_mul, map_one, hr, hs, mul_inv_cancel₀ f.ne_zero]
  have hrunit : IsUnit r := isUnit_iff_exists_inv.mpr ⟨s, hrs⟩
  let e := coordinateRingEquivIntegers W K
  obtain ⟨c, hc⟩ := coordinate_unit_constant W (e.symm r) (hrunit.map e.symm.toMonoidHom)
  refine ⟨c, ?_⟩
  have hcI : algebraMap k (ringOfIntegers k K) c = r := by
    calc
      algebraMap k (ringOfIntegers k K) c =
          (e.restrictScalars k) (algebraMap k W.CoordinateRing c) :=
        ((e.restrictScalars k).commutes c).symm
      _ = r := by
        change e (algebraMap k W.CoordinateRing c) = r
        simpa only [AlgEquiv.apply_symm_apply] using congrArg e hc
  rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) K, hcI, hr]

/-- Positive degree is derived for every actual nonconstant elliptic function. -/
theorem nonconstant_pole_degree_pos (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c) :
    0 < divisorDegree W (poleDivisor W K (Units.mk0 f (by simpa using hf 0))) := by
  by_contra! h
  have hzero := Nat.eq_zero_of_le_zero h
  obtain ⟨c, hc⟩ := constant_of_principalDivisor_zero W K _
    (principalDivisor_eq_zero_of_pole_degree_zero W K _ hzero)
  exact hf c hc.symm

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.coordinate_unit_constant

#print axioms Astra01.EllipticPointDivisor.nonconstant_pole_degree_pos
