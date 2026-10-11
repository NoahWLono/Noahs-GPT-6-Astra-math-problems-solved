import GlobalRecurrenceObstruction
import EllipticProjectiveValue

/-! T2 for genuine projective values of elliptic function-field elements.
The composed rational map is represented by its actual reduced substitution
p(f)/q(f); agreement includes poles on either side. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticTranslation
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : DecidableEq k := Classical.decEq _

theorem point_valuation_translation (G P : W.Point) (f : K) :
    placeValuation k K (placeOfPoint W K P) (translationEquiv W K G f) =
      placeValuation k K (placeOfPoint W K (P + G)) f := by
  rw [← translationPoint_eq_add W K G P]
  change _ = placeValuation k K (placeOfPoint W K
    (pointPullbackEquiv W K (translationEquiv W K G) P)) f
  rw [pointPullback_place, chartPullback_valuation]

theorem projectiveValue_translation (G P : W.Point) (f : K) :
    projectiveValue W K (translationEquiv W K G f) P = projectiveValue W K f (P + G) := by
  cases hv : projectiveValue W K f (P + G) with
  | none =>
    apply (projectiveValue_eq_none_iff W K _ P).mpr
    rw [point_valuation_translation]
    exact (projectiveValue_eq_none_iff W K f (P + G)).mp hv
  | some c =>
    apply (projectiveValue_eq_some_iff W K _ P c).mpr
    rw [← (translationEquiv W K G).commutes c, ← map_sub, point_valuation_translation]
    exact (projectiveValue_eq_some_iff W K f (P + G) c).mp hv

/-- Any finite subset of the cyclic group has at most its exact order points. -/
theorem finite_cyclic_subset_card_le (G : W.Point) (n : ℕ) (hn : 0 < n)
    (horder : addOrderOf G = n) (S : Finset W.Point)
    (hS : ∀ P ∈ S, P ∈ AddSubgroup.zmultiples G) : S.card ≤ n := by
  classical
  have hG : IsOfFinAddOrder G := addOrderOf_pos_iff.mp (by omega)
  let T := Finset.univ.image (fun i : Fin (addOrderOf G) => i.val • G)
  have hsub : S ⊆ T := by
    intro P hP
    obtain ⟨i, hi⟩ := (finEquivZMultiples hG).surjective ⟨P, hS P hP⟩
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩
  calc S.card ≤ T.card := Finset.card_le_card hsub
       _ ≤ (Finset.univ : Finset (Fin (addOrderOf G))).card := Finset.card_image_le
       _ = n := by simp [horder]

/-- Universal T2 bound, including the global-semiconjugacy branch.
There is no distinctness assumption on the two functions: if they coincide,
T1 gives n≤D, while otherwise their actual coincidence divisor gives D+rD. -/
theorem finite_recurrence_agreement_bound (G : W.Point) (n : ℕ) (hn : 2 ≤ n)
    (horder : addOrderOf G = n) (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (S : Finset W.Point) (hS : ∀ P ∈ S, P ∈ AddSubgroup.zmultiples G)
    (hagree : ∀ P ∈ S, projectiveValue W K f (P + G) =
      projectiveValue W K (Polynomial.aeval f p / Polynomial.aeval f q) P) :
    S.card ≤ min n (divisorDegree W
      (poleDivisor W K (Units.mk0 f (by simpa using hf 0))) *
      (max p.natDegree q.natDegree + 1)) := by
  classical
  let e := translationEquiv W K G
  let fu : Kˣ := Units.mk0 f (by simpa using hf 0)
  let u := Units.map e.toMonoidHom fu
  let g := polynomialValueUnit K f hf p hp / polynomialValueUnit K f hf q hq
  let D := divisorDegree W (poleDivisor W K fu)
  have hcard := finite_cyclic_subset_card_le W G n (by omega) horder S hS
  apply le_min hcard
  by_cases he : e f = Polynomial.aeval f p / Polynomial.aeval f q
  · obtain ⟨hd, hdvd⟩ := global_recurrence_obstruction W K G n hn horder f hf p q hq hpq he
    have hpos := nonconstant_pole_degree_pos W K f hf
    have hnD : n ≤ D := Nat.le_of_dvd hpos hdvd
    change S.card ≤ D * (max p.natDegree q.natDegree + 1)
    rw [hd]
    omega
  · have hug : (u : K) ≠ (g : K) := by
      simpa [u, g, fu, polynomialValueUnit] using he
    let h : Kˣ := Units.mk0 ((u : K) - (g : K)) (sub_ne_zero.mpr hug)
    have hbound := projective_agreement_card_le W K u g h rfl S (by
      intro P hP
      apply (projectiveValue_eq_iff_agreement W K (u : K) (g : K) P).mp
      have hv := (projectiveValue_translation W K G P f).trans (hagree P hP)
      simpa [u, g, e, fu, polynomialValueUnit] using hv)
    have huD : divisorDegree W (poleDivisor W K u) = D := pole_degree_automorphism W K e fu
    have hgD : divisorDegree W (poleDivisor W K g) = max p.natDegree q.natDegree * D :=
      nonconstant_rational_composition_degree W K f hf p q hp hq hpq
    rw [huD, hgD] at hbound
    change S.card ≤ D * (max p.natDegree q.natDegree + 1)
    nlinarith

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.finite_recurrence_agreement_bound
