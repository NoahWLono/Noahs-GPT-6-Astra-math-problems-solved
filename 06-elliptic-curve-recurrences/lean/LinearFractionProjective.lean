import RationalProjectiveComposition

/-! Homogeneous-coordinate characterization of the actual projective rational
map (X+b)/(cX+d). This includes both infinity and denominator-zero values. -/
namespace Astra01
noncomputable section
open Polynomial
open scoped Polynomial
variable {k : Type*} [Field k]

def homogeneous : Option k → k × k
  | none => (1,0)
  | some z => (z,1)

theorem linearFraction_projective (b c d : k) (hc : c ≠ 0) (hd : d-b*c ≠ 0)
    (z w : Option k) :
    w = rationalProjectiveMap (X+C b) (C c*X+C d) z ↔
      (homogeneous w).1 * (c*(homogeneous z).1+d*(homogeneous z).2) =
        ((homogeneous z).1+b*(homogeneous z).2)*(homogeneous w).2 := by
  cases z with
  | none =>
    simp only [rationalProjectiveMap, natDegree_X_add_C, natDegree_linear hc,
      lt_self_iff_false, ↓reduceIte, leadingCoeff_X_add_C, leadingCoeff_linear hc]
    cases w with
    | none => simp [homogeneous, hc]
    | some w =>
      simpa only [Option.some.injEq, homogeneous, mul_one, mul_zero, add_zero, one_mul] using
        (eq_div_iff hc : w = 1/c ↔ w*c=1)
  | some z =>
    simp only [rationalProjectiveMap, eval_add, eval_mul, eval_C, eval_X]
    by_cases hq : c*z+d=0
    · have hp : z+b ≠ 0 := by
        intro hp
        apply hd
        linear_combination hq - c * hp
      simp only [hq, ↓reduceIte]
      cases w with
      | none => simp [homogeneous, hq]
      | some w => simp [homogeneous, hq, Ne.symm hp]
    · try simp only [hq, ↓reduceIte]
      cases w with
      | none => simp [homogeneous, hq]
      | some w => simp [homogeneous, hq, eq_div_iff hq]
end
end Astra01
#print axioms Astra01.linearFraction_projective
