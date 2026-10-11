import EllipticCharacterCount
import EllipticQuadraticTwist

namespace Astra01.EllipticTwist
noncomputable section
open WeierstrassCurve.Affine
variable {F : Type*} [Field F] [Fintype F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]
local instance : DecidableEq F := Classical.decEq _

theorem twist_point_count_sum (hF : ringChar F ≠ 2) {d : F} (hd : ¬IsSquare d) :
    (Nat.card W.Point : ℤ) + Nat.card (quadraticTwist W d).Point =
      2*(Fintype.card F : ℤ)+2 := by
  have hd0 : d ≠ 0 := by intro h; subst d; exact hd IsSquare.zero
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  have h8 : (8 : F) ≠ 0 := by convert pow_ne_zero 3 h2 using 1 <;> ring
  letI := quadraticTwist_isElliptic W h2 hd0
  have hχ : quadraticChar F (64*d^3) = -1 := by
    rw [show 64*d^3 = (8*d)^2*d by ring,map_mul,
      quadraticChar_sq_one' (mul_ne_zero h8 hd0),one_mul,
      quadraticChar_neg_one_iff_not_isSquare.mpr hd]
  have hs : (∑ x : F, quadraticChar F (squareDiscriminant (quadraticTwist W d) x)) =
      -(∑ x : F, quadraticChar F (squareDiscriminant W x)) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ (4*d) (mul_ne_zero h4 hd0))
      (fun x => quadraticChar F (squareDiscriminant (quadraticTwist W d) x))]
    change (∑ x : F, quadraticChar F (squareDiscriminant (quadraticTwist W d) (4*d*x))) = _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [quadraticTwist_squareDiscriminant,map_mul,hχ,neg_one_mul]
  rw [point_count_character W hF,point_count_character (quadraticTwist W d) hF,hs]
  ring

end
end Astra01.EllipticTwist
#print axioms Astra01.EllipticTwist.twist_point_count_sum
