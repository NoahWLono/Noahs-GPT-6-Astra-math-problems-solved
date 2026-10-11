import SharpnessActualOrbit
import LinearFractionProjective

/-! The sharpness example and four-map cover in the genuine elliptic group,
using the usual projective extension of the displayed rational functions. -/
namespace Astra01.SharpnessActual
noncomputable section
open Polynomial
open scoped Polynomial
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def xValue (P : curve.Point) : Option (ZMod 11) := (raw P).map Prod.fst

def fractionalMap (b c d : ZMod 11) : Option (ZMod 11) → Option (ZMod 11) :=
  rationalProjectiveMap (X+C b) (C c*X+C d)

theorem exact_agreement_indices (i : Fin 13) :
    xValue (orbit i + generator) = fractionalMap 0 1 5 (xValue (orbit i)) ↔
      i = 1 ∨ i = 6 ∨ i = 8 ∨ i = 9 := by
  rw [← orbit_successor]
  change xValue (orbit (Sharpness.next i)) =
    rationalProjectiveMap (X+C 0) (C 1*X+C 5) (xValue (orbit i)) ↔ _
  rw [linearFraction_projective 0 1 5 (by decide) (by decide)]
  revert i
  decide

theorem actual_four_maps_cover (i : Fin 13) :
    xValue (orbit i + generator) = fractionalMap 4 7 8 (xValue (orbit i)) ∨
    xValue (orbit i + generator) = fractionalMap 3 6 9 (xValue (orbit i)) ∨
    xValue (orbit i + generator) = fractionalMap 10 10 0 (xValue (orbit i)) ∨
    xValue (orbit i + generator) = fractionalMap 1 5 6 (xValue (orbit i)) := by
  rw [← orbit_successor]
  unfold fractionalMap
  rw [linearFraction_projective 4 7 8 (by decide) (by decide),
    linearFraction_projective 3 6 9 (by decide) (by decide),
    linearFraction_projective 10 10 0 (by decide) (by decide),
    linearFraction_projective 1 5 6 (by decide) (by decide)]
  revert i
  decide
end
end Astra01.SharpnessActual
#print axioms Astra01.SharpnessActual.exact_agreement_indices
#print axioms Astra01.SharpnessActual.actual_four_maps_cover
