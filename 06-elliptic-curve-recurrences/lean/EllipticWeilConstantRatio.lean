import EllipticDegreePositive
import EllipticTranslationCovariance

/-! The constant-ratio construction used by the Weil pairing. This is an actual
function-field statement, conditional only on the explicitly stated invariance
of the function's actual point divisor. It does not assert that torsion fibre
divisors have been constructed. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticTranslation
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
local instance : DecidableEq k := Classical.decEq _
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

theorem ratio_constant_of_divisor_eq (f g : Kˣ)
    (h : principalDivisor W K (Additive.ofMul f) = principalDivisor W K (Additive.ofMul g)) :
    ∃ c : k, c ≠ 0 ∧ algebraMap k K c = (f : K) / (g : K) := by
  have hd : principalDivisor W K (Additive.ofMul (f / g)) = 0 := by
    change principalDivisor W K (Additive.ofMul f - Additive.ofMul g) = 0
    rw [map_sub, h, sub_self]
  obtain ⟨c,hc⟩ := constant_of_principalDivisor_zero W K (f / g) hd
  refine ⟨c, ?_, ?_⟩
  · intro hz
    have := (f / g).ne_zero
    rw [← hc, hz, map_zero] at this
    exact this rfl
  · simpa only [Units.val_div_eq_div_val] using hc

theorem translation_ratio_constant (G : W.Point) (f : Kˣ)
    (h : ∀ P : W.Point, principalDivisor W K (Additive.ofMul f) (P + G) =
      principalDivisor W K (Additive.ofMul f) P) :
    ∃ c : k, c ≠ 0 ∧ algebraMap k K c = translationEquiv W K G (f : K) / (f : K) := by
  apply ratio_constant_of_divisor_eq W K (Units.map (translationEquiv W K G).toMonoidHom f) f
  ext P
  rw [principalDivisor_translation, h]
end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.translation_ratio_constant
