import EllipticQuadraticFibers

/-! An explicit scaled quadratic twist of a general Weierstrass equation.
No short-model assumption is made. -/
namespace Astra01.EllipticTwist
noncomputable section
open WeierstrassCurve.Affine
variable {F : Type*} [Field F]
variable (W : WeierstrassCurve.Affine F)

def quadraticTwist (d : F) : WeierstrassCurve.Affine F :=
  ⟨0,d*W.b₂,0,8*d^2*W.b₄,16*d^3*W.b₆⟩

theorem quadraticTwist_delta (d : F) : (quadraticTwist W d).Δ = (4*d)^6*W.Δ := by
  simp only [quadraticTwist,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

theorem quadraticTwist_isElliptic [W.IsElliptic] (h2 : (2 : F) ≠ 0) {d : F} (hd : d ≠ 0) :
    (quadraticTwist W d).IsElliptic := by
  have h4 : (4 : F) ≠ 0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  rw [WeierstrassCurve.isElliptic_iff,quadraticTwist_delta]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero 6 (mul_ne_zero h4 hd))).mul W.isUnit_Δ

theorem quadraticTwist_squareDiscriminant (d x : F) :
    squareDiscriminant (quadraticTwist W d) (4*d*x) = 64*d^3*squareDiscriminant W x := by
  simp only [squareDiscriminant,quadraticTwist,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆]
  ring

end
end Astra01.EllipticTwist
#print axioms Astra01.EllipticTwist.quadraticTwist_isElliptic
#print axioms Astra01.EllipticTwist.quadraticTwist_squareDiscriminant
