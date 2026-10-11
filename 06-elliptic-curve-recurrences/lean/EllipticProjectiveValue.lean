import EllipticCoincidenceDivisor

/-! Actual projective values of elliptic functions at every curve point.
Constant residues are constructed from the degree-one residue fields of the
proved point/place dictionary, including the unique place at infinity. -/
noncomputable section
open scoped RatFunc Polynomial

namespace Astra01
section Residue
variable {k R K : Type*} [Field k] [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [Field K] [Algebra k R] [Algebra R K] [IsFractionRing R K]
  [Algebra k K] [IsScalarTower k R K]

theorem exists_constant_residue_of_degree_one
    (v : IsDedekindDomain.HeightOneSpectrum R)
    (hd : Module.finrank k (R ⧸ v.asIdeal) = 1)
    (f : K) (hf : v.valuation K f ≤ 1) :
    ∃ c : k, v.valuation K (f - algebraMap k K c) < 1 := by
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hf (1 : (WithZero (Multiplicative ℤ))ˣ)
  have hs := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd).2
  obtain ⟨c, hc⟩ := hs (Ideal.Quotient.mk v.asIdeal a)
  have hm : a - algebraMap k R c ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mk v.asIdeal) (algebraMap k R c) = (Ideal.Quotient.mk v.asIdeal) a at hc
    rw [map_sub, hc, sub_self]
  have hav : v.valuation K (algebraMap R K a - algebraMap k K c) < 1 := by
    rw [IsScalarTower.algebraMap_apply k R K, ← map_sub]
    exact (v.valuation_lt_one_iff_mem (K := K) _).mpr hm
  refine ⟨c, ?_⟩
  rw [show f - algebraMap k K c = (f - algebraMap R K a) +
    (algebraMap R K a - algebraMap k K c) by ring]
  apply (v.valuation K).map_add_lt _ hav
  simpa only [Units.val_one, Valuation.map_sub_swap] using ha
end Residue

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

theorem exists_point_constant_residue (f : K) (P : W.Point)
    (hf : placeValuation k K (placeOfPoint W K P) f ≤ 1) :
    ∃ c : k, placeValuation k K (placeOfPoint W K P) (f - algebraMap k K c) < 1 := by
  have hd := placeOfPoint_deg_one W K P
  generalize placeOfPoint W K P = v at *
  cases v with
  | inl v => exact exists_constant_residue_of_degree_one v hd f hf
  | inr v => exact exists_constant_residue_of_degree_one v hd f hf

theorem point_constant_residue_unique (f : K) (P : W.Point) {c d : k}
    (hc : placeValuation k K (placeOfPoint W K P) (f - algebraMap k K c) < 1)
    (hd : placeValuation k K (placeOfPoint W K P) (f - algebraMap k K d) < 1) : c = d := by
  let v := placeValuation k K (placeOfPoint W K P)
  by_contra hne
  have hv : v (algebraMap k K (c - d)) < 1 := by
    rw [map_sub, show algebraMap k K c - algebraMap k K d =
      (f - algebraMap k K d) - (f - algebraMap k K c) by ring]
    exact v.map_sub_lt hd hc
  have he : v (algebraMap k K (c - d)) = 1 :=
    placeValuation_algebraMap_eq_one k K (placeOfPoint W K P)
      (Units.mk0 (c - d) (sub_ne_zero.mpr hne))
  exact (ne_of_lt hv) he

/-- `none` denotes infinity and `some c` the finite projective value c. -/
def projectiveValue (f : K) (P : W.Point) : Option k :=
  if h : 1 < placeValuation k K (placeOfPoint W K P) f then none
  else some (Classical.choose (exists_point_constant_residue W K f P (le_of_not_gt h)))

theorem projectiveValue_eq_none_iff (f : K) (P : W.Point) :
    projectiveValue W K f P = none ↔ 1 < placeValuation k K (placeOfPoint W K P) f := by
  unfold projectiveValue
  split_ifs <;> simp_all

theorem projectiveValue_eq_some_iff (f : K) (P : W.Point) (c : k) :
    projectiveValue W K f P = some c ↔
      placeValuation k K (placeOfPoint W K P) (f - algebraMap k K c) < 1 := by
  unfold projectiveValue
  split_ifs with h
  · have hn : ¬ placeValuation k K (placeOfPoint W K P) (f - algebraMap k K c) < 1 := by
      intro hc
      apply not_le_of_gt h
      rw [← sub_add_cancel f (algebraMap k K c)]
      exact (placeValuation k K (placeOfPoint W K P)).map_add_le hc.le
        (placeValuation_algebraMap_le_one k K (placeOfPoint W K P) c)
    simp [hn]
  · simp only [Option.some.injEq]
    have hc := Classical.choose_spec (exists_point_constant_residue W K f P (le_of_not_gt h))
    constructor
    · intro he; rwa [← he]
    · intro hd; exact point_constant_residue_unique W K f P hc hd

theorem projectiveValue_eq_iff_agreement (f g : K) (P : W.Point) :
    projectiveValue W K f P = projectiveValue W K g P ↔ ProjectiveAgreement W K f g P := by
  constructor
  · intro he
    cases hv : projectiveValue W K f P with
    | none => exact Or.inl ⟨(projectiveValue_eq_none_iff W K f P).mp hv,
        (projectiveValue_eq_none_iff W K g P).mp (he.symm.trans hv)⟩
    | some c => exact Or.inr ⟨c, (projectiveValue_eq_some_iff W K f P c).mp hv,
        (projectiveValue_eq_some_iff W K g P c).mp (he.symm.trans hv)⟩
  · rintro (⟨hf, hg⟩ | ⟨c, hf, hg⟩)
    · exact ((projectiveValue_eq_none_iff W K f P).mpr hf).trans
        ((projectiveValue_eq_none_iff W K g P).mpr hg).symm
    · exact ((projectiveValue_eq_some_iff W K f P c).mpr hf).trans
        ((projectiveValue_eq_some_iff W K g P c).mpr hg).symm

end EllipticPointDivisor
end Astra01
#print axioms Astra01.EllipticPointDivisor.projectiveValue_eq_iff_agreement
