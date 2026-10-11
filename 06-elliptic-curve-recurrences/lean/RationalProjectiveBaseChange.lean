import RationalProjectiveComposition

/-! The ordinary projective extension of a rational expression commutes with
injective field base extension, including finite poles and infinity. -/
namespace Astra01
noncomputable section
open Polynomial
open scoped Polynomial
variable {k l : Type*} [Field k] [Field l]

theorem rationalProjectiveMap_baseChange (φ : k →+* l) (p q : k[X]) (z : Option k) :
    rationalProjectiveMap (p.map φ) (q.map φ) (z.map φ) =
      (rationalProjectiveMap p q z).map φ := by
  cases z with
  | none =>
    simp only [Option.map_none, rationalProjectiveMap,
      natDegree_map_eq_of_injective φ.injective, leadingCoeff_map_of_injective φ.injective]
    split_ifs <;> simp [map_div₀]
  | some z =>
    simp only [Option.map_some, rationalProjectiveMap, eval_map_apply]
    by_cases hq : q.eval z = 0
    · simp [hq]
    · have hq' : φ (q.eval z) ≠ 0 := (_root_.map_ne_zero φ).mpr hq
      simp [hq, hq', map_div₀]
end
end Astra01
#print axioms Astra01.rationalProjectiveMap_baseChange
