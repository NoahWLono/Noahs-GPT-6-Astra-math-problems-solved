import FiniteMenuObstruction

/-! The ordinary reduced rational map on P¹, encoded as Option k, agrees
with actual function-field substitution at every elliptic point. Poles,
finite denominator roots, and the value at infinity are all included. -/
namespace Astra01
noncomputable section
open scoped RatFunc Polynomial
local instance {k : Type*} [Field k] : DecidableEq k := Classical.decEq _
section Residues
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable (v : Valuation K (WithZero (Multiplicative ℤ))) [v.IsTrivialOn k]

theorem polynomial_constant_residue (f : K) (c : k) (hf : HasConstantResidue v f c)
    (p : k[X]) : HasConstantResidue v (Polynomial.aeval f p) (p.eval c) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, Polynomial.eval_add] using hp.add hq
  | monomial n a =>
    simpa only [Polynomial.aeval_monomial, Polynomial.eval_monomial] using
      (HasConstantResidue.constant (v := v) a).mul (hf.pow n)

theorem ratio_at_pole_lt_one (f : K) (hf : 1 < v f)
    (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hd : p.natDegree < q.natDegree) :
    v (Polynomial.aeval f p / Polynomial.aeval f q) < 1 := by
  rw [v.map_div,
    Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X f hf hp,
    Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X f hf hq]
  exact (div_lt_one₀ (pow_pos (zero_lt_one.trans hf) _)).mpr (pow_lt_pow_right₀ hf hd)

theorem ratio_at_pole_gt_one (f : K) (hf : 1 < v f)
    (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hd : q.natDegree < p.natDegree) :
    1 < v (Polynomial.aeval f p / Polynomial.aeval f q) := by
  rw [v.map_div,
    Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X f hf hp,
    Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X f hf hq]
  exact (one_lt_div₀ (pow_pos (zero_lt_one.trans hf) _)).mpr (pow_lt_pow_right₀ hf hd)

theorem equal_degree_remainder (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (hd : p.natDegree = q.natDegree) :
    let t := p - Polynomial.C (p.leadingCoeff / q.leadingCoeff) * q
    t = 0 ∨ t.natDegree < q.natDegree := by
  dsimp only
  by_cases ht : p - Polynomial.C (p.leadingCoeff / q.leadingCoeff) * q = 0
  · exact Or.inl ht
  · apply Or.inr
    apply (Polynomial.natDegree_lt_iff_degree_lt ht).mpr
    have hc : p.leadingCoeff / q.leadingCoeff ≠ 0 :=
      div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) (Polynomial.leadingCoeff_ne_zero.mpr hq)
    have hdeg : p.degree = (Polynomial.C (p.leadingCoeff / q.leadingCoeff) * q).degree := by
      rw [Polynomial.degree_C_mul hc, Polynomial.degree_eq_natDegree hp,
        Polynomial.degree_eq_natDegree hq, hd]
    have hlc : p.leadingCoeff = (Polynomial.C (p.leadingCoeff / q.leadingCoeff) * q).leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      exact (div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hq)).symm
    have hlt := Polynomial.degree_sub_lt hdeg hp hlc
    simpa only [Polynomial.degree_eq_natDegree hp, hd] using hlt

/-- The finite limit at infinity when numerator and denominator have equal degree. -/
theorem ratio_at_pole_equal_degree_residue (f : K) (hf : 1 < v f)
    (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hd : p.natDegree = q.natDegree)
    (hqf : Polynomial.aeval f q ≠ 0) :
    HasConstantResidue v (Polynomial.aeval f p / Polynomial.aeval f q)
      (p.leadingCoeff / q.leadingCoeff) := by
  let c := p.leadingCoeff / q.leadingCoeff
  let t := p - Polynomial.C c * q
  have he : Polynomial.aeval f p / Polynomial.aeval f q - algebraMap k K c =
      Polynomial.aeval f t / Polynomial.aeval f q := by
    simp only [t, map_sub, map_mul, Polynomial.aeval_C]
    field_simp
  change v (Polynomial.aeval f p / Polynomial.aeval f q - algebraMap k K c) < 1
  rw [he]
  rcases equal_degree_remainder p q hp hq hd with ht | ht
  · change t = 0 at ht
    simp [ht]
  · change t.natDegree < q.natDegree at ht
    by_cases ht0 : t = 0
    · simp [ht0]
    · exact ratio_at_pole_lt_one v f hf t q ht0 hq ht
end Residues

/-- Standard projective extension of a reduced rational expression p/q.
At infinity this uses the numerator/denominator degrees and leading coefficients. -/
def rationalProjectiveMap {k : Type*} [Field k] (p q : k[X]) : Option k → Option k
  | some c => if q.eval c = 0 then none else some (p.eval c / q.eval c)
  | none => if q.natDegree < p.natDegree then none
      else if p.natDegree = q.natDegree then some (p.leadingCoeff / q.leadingCoeff)
      else some 0

namespace EllipticPointDivisor
open WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K

theorem projectiveValue_rational_composition (f : K)
    (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : IsCoprime p q) (P : W.Point) :
    projectiveValue W K (Polynomial.aeval f p / Polynomial.aeval f q) P =
      rationalProjectiveMap p q (projectiveValue W K f P) := by
  let v := placeValuation k K (placeOfPoint W K P)
  letI : v.IsTrivialOn k := Valuation.IsTrivialOn.of_le_one v
    (placeValuation_algebraMap_le_one k K _)
  have hqf := nonconstant_polynomial_ne_zero K f hf q hq
  cases hv : projectiveValue W K f P with
  | some c =>
    have hfc : HasConstantResidue v f c := (projectiveValue_eq_some_iff W K f P c).mp hv
    have hpr := polynomial_constant_residue v f c hfc p
    have hqr := polynomial_constant_residue v f c hfc q
    simp only [rationalProjectiveMap]
    split_ifs with hqc
    · apply (projectiveValue_eq_none_iff W K _ P).mpr
      have hpc : p.eval c ≠ 0 := by
        intro hpc
        obtain ⟨a, b, hab⟩ := hpq
        have h := congrArg (Polynomial.eval c) hab
        simp [hpc, hqc] at h
      change 1 < v (Polynomial.aeval f p / Polynomial.aeval f q)
      rw [v.map_div, hpr.valuation_eq_one hpc]
      apply (one_lt_div₀ (v.pos_iff.mpr hqf)).mpr
      simpa only [HasConstantResidue, hqc, map_zero, sub_zero] using hqr
    · apply (projectiveValue_eq_some_iff W K _ P _).mpr
      exact hpr.div hqr hqc
  | none =>
    have hfp : 1 < v f := (projectiveValue_eq_none_iff W K f P).mp hv
    simp only [rationalProjectiveMap]
    split_ifs with hdeg heq
    · exact (projectiveValue_eq_none_iff W K _ P).mpr
        (ratio_at_pole_gt_one v f hfp p q hp hq hdeg)
    · exact (projectiveValue_eq_some_iff W K _ P _).mpr
        (ratio_at_pole_equal_degree_residue v f hfp p q hp hq heq hqf)
    · apply (projectiveValue_eq_some_iff W K _ P 0).mpr
      simp only [map_zero, sub_zero]
      exact ratio_at_pole_lt_one v f hfp p q hp hq (by omega)

end EllipticPointDivisor
end
end Astra01
#print axioms Astra01.EllipticPointDivisor.projectiveValue_rational_composition
