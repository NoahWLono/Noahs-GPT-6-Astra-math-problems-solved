import SharpnessMenuEndpoint
import RationalProjectiveBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! E2's minimum-four statement directly over F11. The proof constructs the
algebraic closure and genuine fraction field internally and transfers every
arbitrary reduced degree-one rational map, not only the four witnesses. -/
namespace Astra01.SharpnessActual
noncomputable section
open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticPointDivisor Polynomial
open scoped RatFunc Polynomial
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem base_field_cover_minimum {ι : Type*} [Fintype ι]
    (p q : ι → (ZMod 11)[X]) (hq : ∀ j, q j ≠ 0)
    (hpq : ∀ j, IsCoprime (p j) (q j))
    (hdegree : ∀ j, max (p j).natDegree (q j).natDegree = 1)
    (hcover : ∀ P : curve.Point, ∃ j,
      xValue (P+generator) = rationalProjectiveMap (p j) (q j) (xValue P)) :
    4 ≤ Fintype.card ι := by
  classical
  let k := AlgebraicClosure (ZMod 11)
  let W := extendedCurve k
  let K := FractionRing W.CoordinateRing
  letI := W.algebraPolynomial K
  letI := W.algebraPolynomial_isScalarTower K
  letI := W.algebraRatFunc K
  letI := W.algebraRatFunc_isScalarTower K
  letI := W.functionField K
  letI := W.isSeparable K
  let φ : ZMod 11 →+* k := algebraMap (ZMod 11) k
  apply no_smaller_cover k K (fun j => (p j).map φ) (fun j => (q j).map φ)
  · intro j
    exact Polynomial.map_ne_zero (hq j)
  · intro j
    exact (hpq j).map (Polynomial.mapRingHom φ)
  · intro j
    simpa only [natDegree_map_eq_of_injective φ.injective] using hdegree j
  · intro P hP
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨j,hj⟩ := hcover (i.val • generator)
    refine ⟨j, ?_⟩
    rw [← map_nsmul, ← map_add, extended_xValue, extended_xValue,
      rationalProjectiveMap_baseChange]
    exact congrArg (Option.map φ) hj

theorem base_field_four_cover (P : curve.Point) : ∃ j : Fin 4,
    xValue (P+generator) =
      rationalProjectiveMap (menuP (ZMod 11) j) (menuQ (ZMod 11) j) (xValue P) := by
  obtain ⟨i,rfl⟩ := orbit_surjective P
  rcases actual_four_maps_cover i with h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩
end
end Astra01.SharpnessActual
#print axioms Astra01.SharpnessActual.base_field_cover_minimum
#print axioms Astra01.SharpnessActual.base_field_four_cover
