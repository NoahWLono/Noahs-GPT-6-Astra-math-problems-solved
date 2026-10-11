import EllipticProjectiveDoubling

/-! Actual function-field iterates for x([2^t]P), their geometric projective
values and their exact exponentially growing pole degree. -/
namespace Astra01.EllipticDuplication
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticPointDivisor Polynomial
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

theorem numerator_ne_zero : numerator W ≠ 0 := by
  intro h
  have hd := numerator_degree W
  simp [h] at hd

theorem denominator_ne_zero (h2 : (2:k) ≠ 0) : denominator W ≠ 0 := by
  intro h
  have hd := denominator_degree W h2
  simp [h] at hd

def iteratedFunction : ℕ → K
  | 0 => XK k K
  | t+1 => aeval (iteratedFunction t) (numerator W) / aeval (iteratedFunction t) (denominator W)

theorem iteratedFunction_nonconstant (h2 : (2:k) ≠ 0) (t : ℕ) :
    ∀ c : k, iteratedFunction W K t ≠ algebraMap k K c := by
  induction t with
  | zero => exact EllipticTranslation.generic_x_ne_constant W K
  | succ t ih =>
    intro c he
    have hpoly : numerator W - C c * denominator W ≠ 0 := by
      intro hp
      have heq := sub_eq_zero.mp hp
      have hle : (C c * denominator W).natDegree ≤ 3 := by
        calc
          _ ≤ (C c).natDegree + (denominator W).natDegree := natDegree_mul_le
          _ = 3 := by rw [natDegree_C, denominator_degree W h2]
      rw [← heq, numerator_degree W] at hle
      omega
    have hq := nonconstant_polynomial_ne_zero K (iteratedFunction W K t) ih
      (denominator W) (denominator_ne_zero W h2)
    have hp := nonconstant_polynomial_ne_zero K (iteratedFunction W K t) ih
      (numerator W-C c*denominator W) hpoly
    apply hp
    simp only [map_sub, map_mul, aeval_C]
    change aeval (iteratedFunction W K t) (numerator W) /
      aeval (iteratedFunction W K t) (denominator W) = algebraMap k K c at he
    exact sub_eq_zero.mpr ((div_eq_iff hq).mp he)

def iteratedUnit (h2 : (2:k) ≠ 0) (t : ℕ) : Kˣ :=
  Units.mk0 (iteratedFunction W K t) (by simpa using iteratedFunction_nonconstant W K h2 t 0)

theorem iterated_degree (h2 : (2:k) ≠ 0) (t : ℕ) :
    divisorDegree W (poleDivisor W K (iteratedUnit W K h2 t)) = 2*4^t := by
  induction t with
  | zero => exact pole_degree_x W K
  | succ t ih =>
    have hf := iteratedFunction_nonconstant W K h2 t
    have hd := nonconstant_rational_composition_degree W K (iteratedFunction W K t) hf
      (numerator W) (denominator W) (numerator_ne_zero W) (denominator_ne_zero W h2)
      (pair_coprime W h2)
    have hu : polynomialValueUnit K (iteratedFunction W K t) hf (numerator W) (numerator_ne_zero W) /
        polynomialValueUnit K (iteratedFunction W K t) hf (denominator W) (denominator_ne_zero W h2) =
        iteratedUnit W K h2 (t+1) := by
      apply Units.ext
      simp [polynomialValueUnit, iteratedUnit, iteratedFunction]
    rw [hu, numerator_degree W, denominator_degree W h2] at hd
    change divisorDegree W (poleDivisor W K (iteratedUnit W K h2 (t+1))) =
      4 * divisorDegree W (poleDivisor W K (iteratedUnit W K h2 t)) at hd
    rw [hd, ih, pow_succ]
    ring

theorem iterated_projective_value (h2 : (2:k) ≠ 0) (t : ℕ) (P : W.Point) :
    projectiveValue W K (iteratedFunction W K t) P = coordinateXValue W ((2^t) • P) := by
  induction t with
  | zero => simpa [iteratedFunction] using projectiveValue_x W K P
  | succ t ih =>
    rw [iteratedFunction, projectiveValue_rational_composition W K _
      (iteratedFunction_nonconstant W K h2 t) _ _ (numerator_ne_zero W)
      (denominator_ne_zero W h2) (pair_coprime W h2), ih,
      ← projective_doubling W h2]
    congr 1
    simp [pow_succ', mul_nsmul, two_nsmul, nsmul_add]
end
end Astra01.EllipticDuplication
#print axioms Astra01.EllipticDuplication.iterated_degree
#print axioms Astra01.EllipticDuplication.iterated_projective_value
