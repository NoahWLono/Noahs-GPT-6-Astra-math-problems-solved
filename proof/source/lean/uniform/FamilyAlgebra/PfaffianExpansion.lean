import FamilyAlgebra.FieldAlgebra

namespace FamilyAlgebra
namespace Pfaffian
variable {E : Type*} [Field E]
abbrev Coordinates (E : Type*) := Fin 6 → E

def pf (x : Coordinates E) : E := x 0*x 5 + x 1*x 4 + x 2*x 3
def polar (x y : Coordinates E) : E :=
  x 0*y 5 + y 0*x 5 + x 1*y 4 + y 1*x 4 + x 2*y 3 + y 2*x 3

def plus (x y : Coordinates E) : Coordinates E := fun i => x i + y i
def scale (a : E) (x : Coordinates E) : Coordinates E := fun i => a*x i

theorem pf_plus (x y : Coordinates E) :
    pf (plus x y) = pf x + pf y + polar x y := by
  simp only [pf, plus, polar, add_mul, mul_add]
  ac_rfl

theorem polar_plus_right (x y z : Coordinates E) :
    polar x (plus y z) = polar x y + polar x z := by
  simp only [polar, plus, add_mul, mul_add]
  ac_rfl

theorem pf_scale (a : E) (x : Coordinates E) :
    pf (scale a x) = a^2 * pf x := by
  simp only [pf, scale, pow_two, mul_add]
  congr 1
  · congr 1 <;> ac_rfl
  · ac_rfl

theorem polar_scale (a b : E) (x y : Coordinates E) :
    polar (scale a x) (scale b y) = a*b*polar x y := by
  simp only [polar, scale, mul_add]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · congr 1 <;> ac_rfl
        · ac_rfl
      · ac_rfl
    · ac_rfl
  · ac_rfl

def vectorSum : List (Coordinates E) → Coordinates E
  | [] => fun _ => 0
  | x :: xs => plus x (vectorSum xs)

def scalarSum : List E → E
  | [] => 0
  | x :: xs => x + scalarSum xs

def pairSum : List (Coordinates E) → E
  | [] => 0
  | x :: xs => scalarSum (xs.map (polar x)) + pairSum xs

theorem polar_vectorSum (x : Coordinates E) (xs : List (Coordinates E)) :
    polar x (vectorSum xs) = scalarSum (xs.map (polar x)) := by
  induction xs with
  | nil => simp [vectorSum, polar, scalarSum]
  | cons y ys ih => simp [vectorSum, polar_plus_right, scalarSum, ih]

/-- The complete diagonal-plus-unordered-pairs expansion for the actual
4x4 alternating Pfaffian, valid for an arbitrary finite list over a field. -/
theorem finite_expansion (xs : List (Coordinates E)) :
    pf (vectorSum xs) = scalarSum (xs.map pf) + pairSum xs := by
  induction xs with
  | nil => simp [vectorSum, pf, scalarSum, pairSum]
  | cons x xs ih =>
    simp only [vectorSum, pf_plus, ih, polar_vectorSum, List.map_cons,
      scalarSum, pairSum]
    ac_rfl

def weightedPairSum : List (E × Coordinates E) → E
  | [] => 0
  | p :: ps => scalarSum (ps.map (fun r => p.1*r.1*polar p.2 r.2)) + weightedPairSum ps

theorem pairSum_weighted (xs : List (E × Coordinates E)) :
    pairSum (xs.map (fun p => scale p.1 p.2)) = weightedPairSum xs := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, pairSum, List.map_map, Function.comp_def,
      polar_scale, ih, weightedPairSum]

/-- Apply finite expansion directly to a weighted family of six-coordinate
alternating matrices. Scalar and polar scaling are proved above. -/
theorem weighted_finite_expansion (xs : List (E × Coordinates E)) :
    pf (vectorSum (xs.map (fun p => scale p.1 p.2))) =
      scalarSum (xs.map (fun p => p.1^2 * pf p.2)) +
        weightedPairSum xs := by
  rw [finite_expansion, List.map_map, pairSum_weighted]
  simp only [Function.comp_def, pf_scale]

/-- Even exponent sums are exactly squared midpoint weights. -/
theorem power_midpoint (a : E) (i j k : Nat) (h : i+j = 2*k) :
    a^i * a^j = (a^k)^2 := by
  rw [← pow_add, h, Nat.mul_comm 2 k, pow_mul]

#print axioms finite_expansion
#print axioms weighted_finite_expansion
end Pfaffian
end FamilyAlgebra
