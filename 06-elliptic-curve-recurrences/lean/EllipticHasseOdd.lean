import EllipticFiniteFieldUpper
import EllipticTwistCount

/-! The classical Hasse discriminant bound in odd characteristic, derived from
the proved actual Frobenius height bound and the actual quadratic-twist count identity. -/
namespace Astra01.EllipticFrobenius
noncomputable section
open WeierstrassCurve.Affine Astra01.EllipticTwist
variable {F : Type*} [Field F] [Fintype F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

theorem finite_field_hasse_discriminant (hF : ringChar F ≠ 2) :
    ((Nat.card W.Point : ℤ) - Fintype.card F - 1)^2 ≤ 4*(Fintype.card F : ℤ) := by
  obtain ⟨d,hd⟩ := FiniteField.exists_nonsquare hF
  have hd0 : d ≠ 0 := by intro h; subst d; exact hd IsSquare.zero
  letI := quadraticTwist_isElliptic W (Ring.two_ne_zero hF) hd0
  have hsum := twist_point_count_sum W hF hd
  have hW := finite_field_upper_discriminant W
  have hT := finite_field_upper_discriminant (quadraticTwist W d)
  rcases hW with hW | hW
  · rcases hT with hT | hT <;> nlinarith [Nat.cast_nonneg (Fintype.card F) (α := ℤ)]
  · exact hW

theorem half_field_card_lt_point_count (hF : ringChar F ≠ 2) (hq : 17 ≤ Fintype.card F) :
    Fintype.card F + 1 < 2*Nat.card W.Point := by
  have hh := finite_field_hasse_discriminant W hF
  by_contra! h
  have hq' : (17 : ℤ) ≤ Fintype.card F := by exact_mod_cast hq
  have h' : 2*(Nat.card W.Point : ℤ) ≤ (Fintype.card F : ℤ)+1 := by exact_mod_cast h
  let q : ℤ := Fintype.card F
  let N : ℤ := Nat.card W.Point
  have hprod := mul_nonneg (show 0 ≤ q+1-2*N by dsimp [q,N]; omega)
    (show 0 ≤ 3*(q+1)-2*N by dsimp [q,N]; omega)
  have hlarge := mul_nonneg (show 0 ≤ q-17 by dsimp [q]; omega)
    (show 0 ≤ q by dsimp [q]; omega)
  change (N-q-1)^2 ≤ 4*q at hh
  nlinarith

end
end Astra01.EllipticFrobenius
#print axioms Astra01.EllipticFrobenius.finite_field_hasse_discriminant
#print axioms Astra01.EllipticFrobenius.half_field_card_lt_point_count
