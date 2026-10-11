import ProjectiveRecurrenceBounds

/-! T1 with a pointwise global recurrence in the actual projective values.
No equality of function-field elements is imposed: it is derived from the
coincidence bound and the proved infinitude of the elliptic point set. -/
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

theorem units_eq_of_projectiveValue_eq (f g : Kˣ)
    (he : ∀ P : W.Point, projectiveValue W K (f : K) P = projectiveValue W K (g : K) P) :
    f = g := by
  classical
  by_contra hne
  have hfg : (f : K) ≠ (g : K) := fun h => hne (Units.ext h)
  let h : Kˣ := Units.mk0 ((f : K) - (g : K)) (sub_ne_zero.mpr hfg)
  obtain ⟨S, hS⟩ := Finset.exists_card_eq (α := W.Point)
    (divisorDegree W (poleDivisor W K f) + divisorDegree W (poleDivisor W K g) + 1)
  have hbound := projective_agreement_card_le W K f g h rfl S
    (fun P _ => (projectiveValue_eq_iff_agreement W K (f : K) (g : K) P).mp (he P))
  omega

/-- Both T1 conclusions from the global equality f(P+G)=R(f(P)) on actual
projective values, in every characteristic. -/
theorem global_projective_recurrence_obstruction (G : W.Point) (n : ℕ) (hn : 2 ≤ n)
    (horder : addOrderOf G = n) (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : k[X]) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (hr : 1 ≤ max p.natDegree q.natDegree)
    (hrec : ∀ P : W.Point, projectiveValue W K f (P + G) =
      rationalProjectiveMap p q (projectiveValue W K f P)) :
    max p.natDegree q.natDegree = 1 ∧
      n ∣ divisorDegree W (poleDivisor W K (Units.mk0 f (by simpa using hf 0))) := by
  have hp := reduced_numerator_ne_zero p q hpq hr
  let fu : Kˣ := Units.mk0 f (by simpa using hf 0)
  let u := Units.map (translationEquiv W K G).toMonoidHom fu
  let g := polynomialValueUnit K f hf p hp / polynomialValueUnit K f hf q hq
  have he : u = g := units_eq_of_projectiveValue_eq W K u g (by
    intro P
    have ht := (projectiveValue_translation W K G P f).trans (hrec P)
    rw [← projectiveValue_rational_composition W K f hf p q hp hq hpq P] at ht
    simpa [u, g, fu, polynomialValueUnit] using ht)
  apply global_recurrence_obstruction W K G n hn horder f hf p q hq hpq
  have hev := congrArg (fun x : Kˣ => (x : K)) he
  simpa [u, g, fu, polynomialValueUnit] using hev

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.global_projective_recurrence_obstruction
