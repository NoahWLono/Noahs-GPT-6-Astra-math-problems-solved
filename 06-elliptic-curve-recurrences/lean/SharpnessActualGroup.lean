import CharacteristicSevenExample
import SharpnessCertificate

/-! The finite F11 certificate is interpreted in the actual Mathlib elliptic
curve group. Fin 11 and ZMod 11 have definitionally identical field residues;
the inverse and addition-formula bridges are proved explicitly. -/
namespace Astra01.SharpnessActual
noncomputable section
open WeierstrassCurve.Affine
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

def curve : WeierstrassCurve.Affine (ZMod 11) := ⟨0, 0, 0, 1, 6⟩
instance : curve.IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  decide

def toZ (x : Sharpness.F) : ZMod 11 := x.val

@[simp] theorem toZ_zero : toZ 0 = 0 := by decide
@[simp] theorem toZ_one : toZ 1 = 1 := by decide
@[simp] theorem toZ_two : toZ 2 = 2 := by decide
@[simp] theorem toZ_three : toZ 3 = 3 := by decide
@[simp] theorem toZ_six : toZ 6 = 6 := by decide
@[simp] theorem toZ_add : ∀ x y : Sharpness.F, toZ (x+y) = toZ x + toZ y := by decide
@[simp] theorem toZ_mul : ∀ x y : Sharpness.F, toZ (x*y) = toZ x * toZ y := by decide
@[simp] theorem toZ_sub : ∀ x y : Sharpness.F, toZ (x-y) = toZ x - toZ y := by decide
@[simp] theorem toZ_eq_iff : ∀ x y : Sharpness.F, toZ x = toZ y ↔ x = y := by decide

theorem inverse_eq (x : Sharpness.F) : toZ (Sharpness.inv x) = (toZ x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, Sharpness.inv]
  · have h : toZ x * toZ (Sharpness.inv x) = 1 := by
      simpa using congrArg toZ (Sharpness.inverse_correct x hx)
    have hxz : toZ x ≠ 0 := fun he => hx ((toZ_eq_iff x 0).mp (he.trans toZ_zero.symm))
    calc toZ (Sharpness.inv x) = (toZ x)⁻¹ * (toZ x * toZ (Sharpness.inv x)) := by
           rw [← mul_assoc, inv_mul_cancel₀ hxz, one_mul]
         _ = (toZ x)⁻¹ := by rw [h, mul_one]

theorem equation_of_certificate (x y : Sharpness.F) (h : Sharpness.onCurve (some (x,y))) :
    curve.Equation (toZ x) (toZ y) := by
  rw [curve.equation_iff]
  have hz := congrArg toZ h
  simpa [curve, pow_succ, mul_assoc] using hz

def lift : (P : Sharpness.Point) → Sharpness.onCurve P → curve.Point
  | none, _ => 0
  | some (x,y), h => Point.mk (equation_of_certificate x y h)

theorem lift_injective {P Q : Sharpness.Point} {hP : Sharpness.onCurve P} {hQ : Sharpness.onCurve Q}
    (h : lift P hP = lift Q hQ) : P = Q := by
  cases P with
  | none => cases Q with
    | none => rfl
    | some q => exact False.elim ((Point.some_ne_zero _).symm h)
  | some p => cases Q with
    | none => exact False.elim (Point.some_ne_zero _ h)
    | some q =>
      rcases p with ⟨x,y⟩
      rcases q with ⟨u,v⟩
      have hh := Point.some.inj h
      have hx := (toZ_eq_iff x u).mp hh.1
      have hy := (toZ_eq_iff y v).mp hh.2
      subst u; subst v; rfl

theorem slope_bridge (x y u v : Sharpness.F) (hxy : ¬(x = u ∧ y + v = 0)) :
    toZ (if x = u then (3*x*x+1) * Sharpness.inv (2*y)
      else (v-y) * Sharpness.inv (u-x)) = curve.slope (toZ x) (toZ u) (toZ y) (toZ v) := by
  by_cases hxu : x = u
  · have hy : toZ y ≠ curve.negY (toZ u) (toZ v) := by
      intro he
      apply hxy
      refine ⟨hxu, ?_⟩
      apply (toZ_eq_iff (y+v) 0).mp
      simpa [curve, negY, eq_neg_iff_add_eq_zero] using he
    simp only [if_pos hxu, toZ_mul, toZ_add, toZ_three, toZ_one, inverse_eq, toZ_two]
    rw [slope, if_pos ((toZ_eq_iff x u).mpr hxu), if_neg hy]
    simp only [curve, negY, zero_mul, sub_zero, mul_zero, zero_add, add_zero]
    simp only [div_eq_mul_inv]
    congr 1 <;> congr 1 <;> ring
  · simp only [if_neg hxu, toZ_mul, toZ_sub, inverse_eq]
    rw [slope, if_neg (by simpa only [toZ_eq_iff] using hxu)]
    rw [← div_eq_mul_inv]
    have he : toZ u - toZ x = -(toZ x - toZ u) := by ring
    have he' : toZ v - toZ y = -(toZ y - toZ v) := by ring
    rw [he, he', neg_div_neg_eq]

def raw : curve.Point → Option (ZMod 11 × ZMod 11)
  | .zero => none
  | .some x y _ => some (x,y)

def mapPoint : Sharpness.Point → Option (ZMod 11 × ZMod 11)
  | none => none
  | some (x,y) => some (toZ x, toZ y)

theorem raw_lift (P : Sharpness.Point) (h : Sharpness.onCurve P) : raw (lift P h) = mapPoint P := by
  cases P with
  | none => rfl
  | some p => rcases p with ⟨x,y⟩; rfl

theorem raw_injective : Function.Injective raw := by
  intro P Q h
  cases P with
  | zero => cases Q with
    | zero => rfl
    | some x y hQ => contradiction
  | some x y hP => cases Q with
    | zero => contradiction
    | some u v hQ =>
      change some (x,y) = some (u,v) at h
      have he := Option.some.inj h
      rcases Prod.mk.inj he with ⟨rfl, rfl⟩
      rfl

theorem lift_add (P Q : Sharpness.Point) (hP : Sharpness.onCurve P) (hQ : Sharpness.onCurve Q)
    (hadd : Sharpness.onCurve (Sharpness.add P Q)) :
    lift (Sharpness.add P Q) hadd = lift P hP + lift Q hQ := by
  apply raw_injective
  rw [raw_lift]
  cases P with
  | none =>
    simp only [Sharpness.add, lift, zero_add]
    exact (raw_lift Q hQ).symm
  | some p =>
    rcases p with ⟨x,y⟩
    cases Q with
    | none => simp only [Sharpness.add, lift, add_zero, raw, mapPoint, Point.mk]
    | some q =>
      rcases q with ⟨u,v⟩
      by_cases hxy : x = u ∧ y + v = 0
      · have hy : toZ y = curve.negY (toZ u) (toZ v) := by
          have hz := congrArg toZ hxy.2
          simpa [negY, curve, eq_neg_iff_add_eq_zero] using hz
        simp only [Sharpness.add, if_pos hxy, mapPoint, lift, Point.mk]
        rw [Point.add_of_Y_eq ((toZ_eq_iff x u).mpr hxy.1) hy]
        rfl
      · have hxy' : ¬(toZ x = toZ u ∧ toZ y = curve.negY (toZ u) (toZ v)) := by
          rintro ⟨hx, hy⟩
          apply hxy
          refine ⟨(toZ_eq_iff x u).mp hx, ?_⟩
          apply (toZ_eq_iff (y+v) 0).mp
          simpa [curve, negY, eq_neg_iff_add_eq_zero] using hy
        simp only [Sharpness.add, if_neg hxy, mapPoint, lift, Point.mk]
        rw [Point.add_some hxy']
        simp only [raw, Option.some.injEq, Prod.mk.injEq, toZ_sub, toZ_mul,
          slope_bridge x y u v hxy, addX, addY, negAddY, negY, curve]
        constructor <;> ring

theorem certificate_orbit_on_curve (i : Fin 13) : Sharpness.onCurve (Sharpness.orbit i) := by
  have h : ∀ j : Fin 13, Sharpness.onCurve (Sharpness.orbit j) := by decide
  exact h i

def orbit (i : Fin 13) : curve.Point := lift (Sharpness.orbit i) (certificate_orbit_on_curve i)
def generator : curve.Point := orbit 1

theorem orbit_injective : Function.Injective orbit := by
  intro i j h
  exact Sharpness.orbit_injective i j (lift_injective h)

theorem orbit_addition (i j : Fin 13) : orbit (i+j) = orbit i + orbit j := by
  have he := Sharpness.orbit_addition i j
  have hsum : Sharpness.onCurve (Sharpness.add (Sharpness.orbit i) (Sharpness.orbit j)) :=
    he ▸ certificate_orbit_on_curve (i+j)
  have ht := lift_add (Sharpness.orbit i) (Sharpness.orbit j)
    (certificate_orbit_on_curve i) (certificate_orbit_on_curve j) hsum
  simpa only [he, orbit] using ht

end
end Astra01.SharpnessActual
#print axioms Astra01.SharpnessActual.lift_add
#print axioms Astra01.SharpnessActual.orbit_addition
