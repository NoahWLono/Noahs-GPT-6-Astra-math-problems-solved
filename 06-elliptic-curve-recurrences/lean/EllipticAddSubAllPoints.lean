import EllipticAddSubCompatibility

/-! All exceptional cases in the actual symmetric-square addition/subtraction
map, over every field (no algebraic-closure assumption on the function field). -/
namespace Astra01.EllipticAddSub
noncomputable section
open WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
local instance : DecidableEq k := Classical.decEq _

theorem mapVector_same (P : W.Point) : ∃ c : k, c ≠ 0 ∧
    mapVector W (P.sym2x P) = c • ((P+P).sym2x (P-P)) := by
  cases P with
  | zero =>
    refine ⟨1, one_ne_zero, ?_⟩
    change mapVector W ((0 : W.Point).sym2x 0) = (1 : k) • ((0+0 : W.Point).sym2x (0-0))
    simp only [zero_add, sub_self, one_smul, Point.sym2x_zero_zero]
    ext i
    fin_cases i <;> simp [mapVector, WeierstrassCurve.addSubMap]
  | some x y h =>
    let U := x^4-W.b₄*x^2-2*W.b₆*x-W.b₈
    let D := 4*x^3+W.b₂*x^2+2*W.b₄*x+W.b₆
    have hd : D = (y-W.negY x y)^2 := by
      have he := (W.equation_iff x y).mp h.1
      dsimp [D, negY]
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      linear_combination -4*he
    have hm : mapVector W ((Point.some x y h).sym2x (Point.some x y h)) = ![U,D,0] := by
      rw [Point.sym2x_some_some, mapVector_pair]
      ext i
      fin_cases i <;> simp [U,D] <;> ring
    rw [hm]
    by_cases hy : y = W.negY x y
    · have hD : D = 0 := by rw [hd, sub_eq_zero.mpr hy, zero_pow (by decide)]
      have hU : U ≠ 0 := by
        intro hz
        apply W.addSubMap_ne_zero (Point.sym2x_ne_zero (Point.some x y h) (Point.some x y h))
        change mapVector W _ = 0
        rw [hm,hz,hD]
        ext i
        fin_cases i <;> simp
      refine ⟨U,hU,?_⟩
      rw [Point.add_self_of_Y_eq hy, sub_self]
      simp [hD]
    · have hD : D ≠ 0 := hd ▸ pow_ne_zero 2 (sub_ne_zero.mpr hy)
      have hU : U = D * W.addX x x (W.slope x x y y) := by
        have he := (W.equation_iff x y).mp h.1
        rw [hd, W.slope_of_Y_ne rfl hy]
        unfold addX
        field_simp [sub_ne_zero.mpr hy]
        dsimp [U, negY]
        simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        linear_combination (W.a₁^2+4*W.a₂+8*x)*he
      refine ⟨D,hD,?_⟩
      rw [Point.add_self_of_Y_ne hy, sub_self, Point.sym2x_some_zero]
      ext i
      fin_cases i <;> simp [hU]

theorem mapVector_zero (P : W.Point) :
    mapVector W ((0 : W.Point).sym2x P) = P.sym2x (-P) := by
  cases P with
  | zero =>
    change mapVector W ((0 : W.Point).sym2x 0) = (0 : W.Point).sym2x (-0)
    simp only [neg_zero, Point.sym2x_zero_zero]
    ext i
    fin_cases i <;> simp [mapVector, WeierstrassCurve.addSubMap]
  | some x y h =>
    simp only [Point.sym2x_zero_some, Point.sym2x_neg_right, Point.sym2x_some_some]
    ext i
    fin_cases i <;> simp [mapVector, WeierstrassCurve.addSubMap] <;> ring

/-- Genuine addition/subtraction compatibility at every point, including all
infinities and tangent/2-torsion cases. The scalar is explicitly nonzero. -/
theorem mapVector_add_sub (P Q : W.Point) : ∃ c : k, c ≠ 0 ∧
    mapVector W (P.sym2x Q) = c • ((P+Q).sym2x (P-Q)) := by
  cases P with
  | zero =>
    refine ⟨1,one_ne_zero,?_⟩
    change mapVector W ((0 : W.Point).sym2x Q) = (1 : k) • ((0+Q).sym2x (0-Q))
    simpa using mapVector_zero W Q
  | some x y h =>
    cases Q with
    | zero =>
      refine ⟨1,one_ne_zero,?_⟩
      change mapVector W ((Point.some x y h).sym2x (0 : W.Point)) =
        (1 : k) • (((Point.some x y h : W.Point)+0).sym2x (Point.some x y h-0))
      rw [Point.sym2x_comm, mapVector_zero, Point.sym2x_neg_right]
      simp
    | some u v j =>
      by_cases hx : x = u
      · have hp : (Point.some x y h : W.Point) = Point.some u v j ∨
            (Point.some x y h : W.Point) = -Point.some u v j := by
          rcases W.Y_eq_of_X_eq h.1 j.1 hx with hy | hy
          · left
            rw [Point.some.injEq]
            exact ⟨hx,hy⟩
          · right
            rw [Point.neg_some, Point.some.injEq]
            exact ⟨hx,hy⟩
        rcases hp with hp | hp
        · rw [hp]
          exact mapVector_same W _
        · rw [hp, Point.sym2x_neg_left]
          obtain ⟨c,hc,he⟩ := mapVector_same W (Point.some u v j)
          refine ⟨c,hc,?_⟩
          rw [neg_add_cancel, show -(Point.some u v j : W.Point) - Point.some u v j =
            -((Point.some u v j : W.Point)+Point.some u v j) by abel,
            Point.sym2x_neg_right,
            Point.sym2x_comm (0 : W.Point) ((Point.some u v j : W.Point)+Point.some u v j)]
          simpa only [sub_self] using he
      · exact ⟨(u-x)^2,pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hx)), mapVector_distinct W h j hx⟩

end
end Astra01.EllipticAddSub
#print axioms Astra01.EllipticAddSub.mapVector_same

#print axioms Astra01.EllipticAddSub.mapVector_add_sub
