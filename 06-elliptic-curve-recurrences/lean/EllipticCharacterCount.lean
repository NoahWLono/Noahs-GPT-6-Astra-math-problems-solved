import EllipticQuadraticFibers
import Mathlib.Data.Fintype.Sigma

namespace Astra01.EllipticTwist
noncomputable section
open WeierstrassCurve.Affine
variable {F : Type*} [Field F] [Fintype F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]
local instance : DecidableEq F := Classical.decEq _

theorem point_count_fibers :
    Nat.card W.Point = 1 + ∑ x : F, Nat.card {y : F // W.Equation x y} := by
  classical
  rw [Nat.card_congr W.pointEquiv]
  change Nat.card (Option {xy : F × F // W.Equation xy.1 xy.2}) = _
  rw [Nat.card_eq_fintype_card,Fintype.card_option,← Nat.card_eq_fintype_card,
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype W.Equation),Nat.card_sigma]
  omega

theorem point_count_character (hF : ringChar F ≠ 2) :
    (Nat.card W.Point : ℤ) = (Fintype.card F : ℤ) + 1 +
      ∑ x : F, quadraticChar F (squareDiscriminant W x) := by
  rw [point_count_fibers]
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_sum,affine_fiber_count W hF,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  ring

end
end Astra01.EllipticTwist
#print axioms Astra01.EllipticTwist.point_count_character
