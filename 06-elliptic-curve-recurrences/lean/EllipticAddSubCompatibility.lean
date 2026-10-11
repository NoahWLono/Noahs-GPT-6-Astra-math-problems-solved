import EllipticAddSubAlgebra
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
import EllipticProjectiveDoubling

/-! Actual point compatibility for the symmetric-square addition/subtraction
map. Mathlib supplies its homogeneous Bézout identity; this module supplies
its connection to the genuine elliptic group law. -/
namespace Astra01.EllipticAddSub
noncomputable section
open WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k)
local instance : DecidableEq k := Classical.decEq _

def mapVector (z : Fin 3 → k) : Fin 3 → k := fun i => (W.addSubMap i).eval z

theorem mapVector_pair (x u : k) : mapVector W ![x*u,x+u,1] =
    ![(x*u)^2-W.b₄*(x*u)-W.b₆*(x+u)-W.b₈,
      2*(x+u)*(x*u)+W.b₂*(x*u)+W.b₄*(x+u)+W.b₆,(u-x)^2] := by
  ext i
  fin_cases i <;> simp [mapVector, WeierstrassCurve.addSubMap] <;> ring

theorem addX_chord {x u : k} (y v : k) (hxu : x ≠ u) :
    W.addX x u (W.slope x u y v) = chordNumerator W x u y v / (u-x)^2 := by
  rw [W.slope_of_X_ne hxu]
  unfold addX chordNumerator
  field_simp [sub_ne_zero.mpr hxu, sub_ne_zero.mpr hxu.symm]
  <;> ring

theorem mapVector_distinct {x u y v : k} (h : W.Nonsingular x y)
    (j : W.Nonsingular u v) (hxu : x ≠ u) :
    mapVector W ((Point.some x y h).sym2x (Point.some u v j)) =
      (u-x)^2 • (((Point.some x y h : W.Point) + Point.some u v j).sym2x
        ((Point.some x y h : W.Point) - Point.some u v j)) := by
  have hd := sub_ne_zero.mpr hxu.symm
  have hs := chordNumerator_sum W h.1 j.1
  have hp := chordNumerator_product W h.1 j.1
  have hU : (x*u)^2-W.b₄*(x*u)-W.b₆*(x+u)-W.b₈ =
      chordNumerator W x u y v * chordNumerator W x u y (W.negY u v) / (u-x)^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hd)).mpr
    linear_combination -hp
  have hsub := sub_eq_add_neg (Point.some x y h : W.Point) (Point.some u v j)
  rw [Point.sym2x_some_some, mapVector_pair, hsub, Point.neg_some,
    Point.add_of_X_ne hxu, Point.add_of_X_ne hxu, Point.sym2x_some_some,
    addX_chord W y v hxu, addX_chord W y (W.negY u v) hxu, hU, ← hs]
  ext i
  fin_cases i <;> simp <;> field_simp [hd] <;> ring
end
end Astra01.EllipticAddSub
#print axioms Astra01.EllipticAddSub.mapVector_distinct
