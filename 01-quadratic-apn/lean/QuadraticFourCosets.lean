import QuadraticFourRadical
import QuadraticFourWeights
import QuadraticFourPlane

set_option maxHeartbeats 2000000
namespace BooleanANF.QuadraticFour

theorem degree_translate {q : V → F₂} (hq : HasDegreeLE q 2) (a : V) :
    HasDegreeLE (fun x => q (x+a)) 2 := by
  apply hq.comp_affine
  intro i
  exact (degree_coordinate i).add ((degree_const (a i)).mono (by omega))

theorem weight_translate (q : V → F₂) (a : V) : weight (fun x => q (x+a)) = weight q := by
  let e : V ≃ V := ⟨fun x => x+a, fun x => x+a,
    fun x => by change (x+a)+a=x; rw [add_assoc, vec_add_self, add_zero],
    fun x => by change (x+a)+a=x; rw [add_assoc, vec_add_self, add_zero]⟩
  exact weight_equiv q e

theorem polar_translate {q : V → F₂} (hq : HasDegreeLE q 2) (a x y : V) :
    polar (fun z => q (z+a)) x y = polar q x y := by
  apply quadratic_induction hq
  intro A b c d e f g h i j k
  simp [polar, poly, Pi.add_apply, Pi.zero_apply]
  ring_nf
  simp only [show (2 : F₂) = 0 from rfl, show (4 : F₂) = 0 from rfl, mul_zero, add_zero, zero_add]

theorem weight_radicalIndicator (q : V → F₂) :
    weight (radicalIndicator q) = (radicalPoints q).card := by
  rw [weight_eq_support_card]
  congr 1
  ext x
  simp [radicalIndicator, radicalPoints]

/-- Rank-two cost-four rows are precisely the indicators of radical cosets
which do not contain zero. The coset is expressed in the original coordinates. -/
theorem cost_four_iff_nonzero_coset {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 4) :
    cost q = 4 ↔ ∃ a : V, ¬ IsRadical q a ∧
      ∀ x, q x = radicalIndicator q (x+a) := by
  constructor
  · intro hc
    have hw := radical_four_weights hq hr
    have hb := ZMod.val_lt (q 0)
    have hc' := hc
    unfold cost at hc'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    have hw4 : weight q = 4 := by omega
    have hq0 : q 0 = 0 := by
      apply ZMod.val_injective 2
      change (q 0).val = 0
      omega
    have hs : (supportPoints q).Nonempty := by
      apply Finset.card_pos.mp
      change 0 < (Finset.univ.filter (fun x => q x = 1)).card
      rw [← weight_eq_support_card, hw4]
      decide
    obtain ⟨a,ha⟩ := hs
    have hqa : q a = 1 := (Finset.mem_filter.mp ha).2
    let p : V → F₂ := fun x => q (x+a)
    have hp : HasDegreeLE p 2 := degree_translate hq a
    have hpc : cost p = 2 := by
      change (weight (fun x => q (x+a)) : ℤ) - 2 * ((q (0+a)).val : ℤ) = 2
      rw [weight_translate, hw4, zero_add, hqa]
      decide
    have he : p = radicalIndicator q := (cost_two_eq_radical hp hpc).trans
      (radicalIndicator_eq_of_polar_eq (fun x y => polar_translate hq a x y))
    have he' (x : V) : q x = radicalIndicator q (x+a) := by
      have hh := congrFun he (x+a)
      simpa only [p, add_assoc, vec_add_self, add_zero] using hh
    refine ⟨a, ?_, he'⟩
    intro har
    have hh := he' 0
    simp [radicalIndicator, har, hq0] at hh
  · rintro ⟨a,ha,he⟩
    have hfun : q = fun x => radicalIndicator q (x+a) := funext he
    have hw : weight q = 4 := by
      calc
        weight q = weight (fun x => radicalIndicator q (x+a)) := congrArg weight hfun
        _ = weight (radicalIndicator q) := weight_translate _ a
        _ = 4 := (weight_radicalIndicator q).trans hr
    have hq0 : q 0 = 0 := by simpa [radicalIndicator, ha] using he 0
    simp [cost, hw, hq0]

/-- Every nonzero radical coset actually occurs as a cost-four perturbation
with the same polar form. -/
theorem nonzero_coset_perturbation {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 4) {a : V} (ha : ¬ IsRadical q a) :
    let p := fun x => radicalIndicator q (x+a)
    HasDegreeLE p 2 ∧ (∀ x y, polar p x y = polar q x y) ∧ cost p = 4 := by
  dsimp only
  refine ⟨degree_translate (radicalIndicator_degree hq hr) a, ?_, ?_⟩
  · intro x y
    rw [polar_translate (radicalIndicator_degree hq hr), radicalIndicator_polar hq hr]
  · unfold cost
    rw [weight_translate, weight_radicalIndicator, hr]
    simp [radicalIndicator, ha]

#print axioms cost_four_iff_nonzero_coset
end BooleanANF.QuadraticFour
