/-!
Finite certificate for ASTRA-01 E1, checked by Lean's kernel (no native_decide).
This defines the explicit F_11 affine addition formulas; it does not identify
this implementation with mathlib's abstract elliptic-curve group or prove
that the geometric x morphism has degree two.
-/
namespace Astra01.Sharpness
abbrev F := Fin 11
abbrev Point := Option (F × F)
abbrev ProjectiveValue := F × F

def inv (x : F) : F := x ^ 9

def onCurve : Point → Prop
  | none => True
  | some (x,y) => y*y = x*x*x + x + 6
instance (P : Point) : Decidable (onCurve P) := by
  cases P with
  | none => exact inferInstanceAs (Decidable True)
  | some P => exact inferInstanceAs (Decidable (_ = _))

def add : Point → Point → Point
  | none, Q => Q
  | P, none => P
  | some (x,y), some (u,v) =>
    if x = u ∧ y + v = 0 then none else
    let slope := if x = u then (3*x*x + 1) * inv (2*y)
                 else (v-y) * inv (u-x)
    let w := slope*slope - x - u
    some (w, slope*(x-w)-y)

def orbit (i : Fin 13) : Point := ([
  none, some (2,4), some (5,9), some (8,8), some (10,9),
  some (3,5), some (7,2), some (7,9), some (3,6), some (10,2),
  some (8,3), some (5,2), some (2,7)] : List Point)[i.val]'(by exact i.isLt)

def next (i : Fin 13) : Fin 13 := i + 1

def xcoord : Point → ProjectiveValue
  | none => (1,0)
  | some (x,_) => (x,1)

def mobius (a b c d : F) (z : ProjectiveValue) : ProjectiveValue :=
  (a*z.1+b*z.2, c*z.1+d*z.2)

def projectivelyEqual (z w : ProjectiveValue) : Bool :=
  z.1*w.2 == w.1*z.2

def matchingIndices (a b c d : F) : List Nat :=
  (List.finRange 13).filterMap fun i =>
    if projectivelyEqual (xcoord (orbit (next i)))
        (mobius a b c d (xcoord (orbit i))) then some i.val else none

/-- Every nonzero residue has the claimed inverse. -/
theorem inverse_correct : ∀ x : F, x ≠ 0 → x * inv x = 1 := by decide
/-- The discriminant factor 4a³+27b² is nonzero for a=1,b=6. -/
theorem nonsingular : (4 * (1 : F)^3 + 27 * (6 : F)^2) ≠ 0 := by decide
/-- The table lists each point satisfying the affine equation, plus infinity, exactly once. -/
theorem orbit_complete : (∃ i : Fin 13, orbit i = none) ∧
  ∀ x y : F, onCurve (some (x,y)) ↔ ∃ i : Fin 13, orbit i = some (x,y) := by decide
theorem orbit_injective : ∀ i j : Fin 13, orbit i = orbit j → i = j := by decide
/-- The table is an actual successive-addition orbit for the displayed formula. -/
theorem orbit_successor : ∀ i : Fin 13, add (orbit i) (some (2,4)) = orbit (next i) := by decide
/-- Stronger finite cross-check: the whole addition table agrees with Z/13 labels. -/
theorem orbit_addition : ∀ i j : Fin 13, add (orbit i) (orbit j) = orbit (i+j) := by decide
def repeatedAdd : Nat → Point
  | 0 => none
  | k+1 => add (repeatedAdd k) (some (2,4))
/-- Exact order of the displayed generator under the verified addition table. -/
theorem generator_exact_order : repeatedAdd 13 = none ∧
    ∀ i : Fin 12, repeatedAdd (i.val+1) ≠ none := by decide
/-- Both homogeneous coordinate pairs used in E1 are valid. -/
theorem valid_projective_pairs : ∀ i : Fin 13,
  xcoord (orbit i) ≠ (0,0) ∧ mobius 1 0 1 5 (xcoord (orbit i)) ≠ (0,0) := by decide
theorem witness_invertible : (1 * 5 - 0 * 1 : F) ≠ 0 := by decide
theorem exact_four_agreements : matchingIndices 1 0 1 5 = [1,6,8,9] := by decide
theorem exact_four_count : (matchingIndices 1 0 1 5).length = 4 := by decide
/-- The four maps displayed in the manuscript cover every index. -/
theorem four_maps_cover : ∀ i : Fin 13,
  projectivelyEqual (xcoord (orbit (next i))) (mobius 1 4 7 8 (xcoord (orbit i))) = true ∨
  projectivelyEqual (xcoord (orbit (next i))) (mobius 1 3 6 9 (xcoord (orbit i))) = true ∨
  projectivelyEqual (xcoord (orbit (next i))) (mobius 1 10 10 0 (xcoord (orbit i))) = true ∨
  projectivelyEqual (xcoord (orbit (next i))) (mobius 1 1 5 6 (xcoord (orbit i))) = true := by decide
theorem cover_maps_invertible :
  (1*8-4*7 : F) ≠ 0 ∧ (1*9-3*6 : F) ≠ 0 ∧
  (1*0-10*10 : F) ≠ 0 ∧ (1*6-1*5 : F) ≠ 0 := by decide

#print axioms inverse_correct
#print axioms nonsingular
#print axioms orbit_complete
#print axioms orbit_injective
#print axioms orbit_successor
#print axioms orbit_addition
#print axioms generator_exact_order
#print axioms valid_projective_pairs
#print axioms witness_invertible
#print axioms exact_four_agreements
#print axioms exact_four_count
#print axioms four_maps_cover
#print axioms cover_maps_invertible
end Astra01.Sharpness
