import EllipticDegreePositive

/-! The degree-one conclusion of T1, derived from actual elliptic
function-field automorphisms, genuine divisor degrees, and rational composition.
The separate n-divides-D conclusion is not asserted in this module. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K

include W in
/-- A nonconstant elliptic function semiconjugating a genuine field automorphism
to a reduced rational map forces that rational map to have degree one. -/
theorem semiconjugacy_degree_one (e : K ≃ₐ[k] K) (f : K)
    (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (he : e f = Polynomial.aeval f p / Polynomial.aeval f q) :
    max p.natDegree q.natDegree = 1 := by
  let fu : Kˣ := Units.mk0 f (by simpa using hf 0)
  have hu : Units.map e.toMonoidHom fu =
      polynomialValueUnit K f hf p hp / polynomialValueUnit K f hf q hq := by
    apply Units.ext
    simpa [fu, polynomialValueUnit] using he
  have hd := pole_degree_automorphism W K e fu
  rw [hu, nonconstant_rational_composition_degree W K f hf p q hp hq hpq] at hd
  have hpos := nonconstant_pole_degree_pos W K f hf
  apply mul_right_cancel₀ (Nat.ne_of_gt hpos)
  simpa only [one_mul] using hd

/-- The actual translation specialization of the degree-one part of T1. -/
theorem translation_semiconjugacy_degree_one (G : W.Point) (f : K)
    (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : k[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (he : Astra01.EllipticTranslation.translationEquiv W K G f =
      Polynomial.aeval f p / Polynomial.aeval f q) :
    max p.natDegree q.natDegree = 1 :=
  semiconjugacy_degree_one W K (Astra01.EllipticTranslation.translationEquiv W K G)
    f hf p q hp hq hpq he

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.translation_semiconjugacy_degree_one
