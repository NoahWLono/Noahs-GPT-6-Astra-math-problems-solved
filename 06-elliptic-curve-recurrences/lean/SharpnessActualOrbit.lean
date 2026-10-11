import SharpnessActualGroup

/-! Completeness, exact group cardinality and generator order for the F11
sharpness curve, using the genuine elliptic group and the checked certificate. -/
namespace Astra01.SharpnessActual
noncomputable section
open WeierstrassCurve.Affine
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem toZ_surjective : Function.Surjective toZ := by decide

theorem certificate_of_equation (x y : Sharpness.F)
    (h : curve.Equation (toZ x) (toZ y)) : Sharpness.onCurve (some (x,y)) := by
  have he := (curve.equation_iff _ _).mp h
  have hz : toZ (y*y) = toZ (x*x*x+x+6) := by
    simpa [curve, pow_succ, mul_assoc] using he
  exact (toZ_eq_iff _ _).mp hz

theorem orbit_zero : orbit 0 = 0 := rfl

theorem orbit_surjective : Function.Surjective orbit := by
  intro P
  cases P with
  | zero => exact ⟨0, orbit_zero⟩
  | some a b hP =>
    obtain ⟨x, rfl⟩ := toZ_surjective a
    obtain ⟨y, rfl⟩ := toZ_surjective b
    have hc := certificate_of_equation x y hP.1
    obtain ⟨i, hi⟩ := (Sharpness.orbit_complete.2 x y).mp hc
    refine ⟨i, ?_⟩
    apply raw_injective
    change raw (lift (Sharpness.orbit i) _) = some (toZ x, toZ y)
    rw [raw_lift, hi]
    rfl

def orbitEquiv : Fin 13 ≃ curve.Point := Equiv.ofBijective orbit ⟨orbit_injective, orbit_surjective⟩

instance : Finite curve.Point := Finite.of_equiv (Fin 13) orbitEquiv

theorem curve_point_count : Nat.card curve.Point = 13 := by
  rw [← Nat.card_congr orbitEquiv]
  simp

theorem generator_ne_zero : generator ≠ 0 := by
  intro h
  have he : orbit 1 = orbit 0 := h.trans orbit_zero.symm
  have hi : (1 : Fin 13) = 0 := orbit_injective he
  exact (by decide : (1 : Fin 13) ≠ 0) hi

theorem generator_order : addOrderOf generator = 13 := by
  have hd : addOrderOf generator ∣ 13 := by
    simpa only [curve_point_count] using addOrderOf_dvd_natCard generator
  rcases (Nat.dvd_prime (by decide : Nat.Prime 13)).mp hd with h | h
  · exact False.elim (generator_ne_zero (by have hz := addOrderOf_nsmul_eq_zero generator; simpa [h] using hz))
  · exact h

theorem orbit_successor (i : Fin 13) : orbit (Sharpness.next i) = orbit i + generator :=
  orbit_addition i 1

end
end Astra01.SharpnessActual
#print axioms Astra01.SharpnessActual.orbit_surjective
#print axioms Astra01.SharpnessActual.curve_point_count
#print axioms Astra01.SharpnessActual.generator_order
