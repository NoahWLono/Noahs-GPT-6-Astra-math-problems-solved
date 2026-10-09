import QuadraticFourAffine

set_option maxHeartbeats 2000000
namespace BooleanANF.QuadraticFour

theorem affine_poly_degree (a b c d e : F₂) :
    HasDegreeLE (poly a b c d e 0 0 0 0 0 0) 1 := by
  have ha : HasDegreeLE (fun _ : V => a) 1 := (degree_const a).mono (by omega)
  have hb : HasDegreeLE (fun x : V => b * x 0) 1 := (degree_coordinate 0).smul b
  have hc : HasDegreeLE (fun x : V => c * x 1) 1 := (degree_coordinate 1).smul c
  have hd : HasDegreeLE (fun x : V => d * x 2) 1 := (degree_coordinate 2).smul d
  have he : HasDegreeLE (fun x : V => e * x 3) 1 := (degree_coordinate 3).smul e
  have hp : poly a b c d e 0 0 0 0 0 0 =
      fun x : V => a + b*x 0 + c*x 1 + d*x 2 + e*x 3 := by
    funext x
    simp [poly]
  rw [hp]
  exact (((ha.add hb).add hc).add hd).add he

/-- A quadratic with zero actual polar has canonical degree at most one. -/
theorem degree_one_of_zero_polar {q : V → F₂} (hq : HasDegreeLE q 2)
    (hzero : ∀ x y, polar q x y = 0) : HasDegreeLE q 1 := by
  revert hzero
  apply quadratic_induction hq
  intro a b c d e f g h i j k H
  have hf := H ![1,0,0,0] ![0,1,0,0]
  have hg := H ![1,0,0,0] ![0,0,1,0]
  have hh := H ![1,0,0,0] ![0,0,0,1]
  have hi := H ![0,1,0,0] ![0,0,1,0]
  have hj := H ![0,1,0,0] ![0,0,0,1]
  have hk := H ![0,0,1,0] ![0,0,0,1]
  simp [polar_poly] at hf hg hh hi hj hk
  subst f; subst g; subst h; subst i; subst j; subst k
  exact affine_poly_degree a b c d e

theorem polar_add (p q : V → F₂) (x y : V) :
    polar (fun z => p z + q z) x y = polar p x y + polar q x y := by
  unfold polar
  ring

/-- Two quadratics with the same polar differ by an actual affine Boolean function. -/
theorem same_polar_affine_difference {p q : V → F₂}
    (hp : HasDegreeLE p 2) (hq : HasDegreeLE q 2)
    (hpol : ∀ x y, polar p x y = polar q x y) :
    HasDegreeLE (fun x => p x + q x) 1 := by
  apply degree_one_of_zero_polar (hp.add hq)
  intro x y
  rw [polar_add, hpol, CharTwo.add_self_eq_zero]

#print axioms same_polar_affine_difference
end BooleanANF.QuadraticFour
