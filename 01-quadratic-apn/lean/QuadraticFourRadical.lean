import QuadraticFourPolar
import QuadraticFourDegree
import QuadraticFourPolarEnumeration
import QuadraticFourRadicalRepresentative

namespace BooleanANF.QuadraticFour

theorem quadratic_induction {P : (V → F₂) → Prop} {q : V → F₂}
    (hq : HasDegreeLE q 2)
    (hp : ∀ a b c d e f g h i j k : F₂, P (poly a b c d e f g h i j k)) : P q := by
  rw [← representation hq, eval_eq_poly]
  exact hp _ _ _ _ _ _ _ _ _ _ _

/-- Radical cardinality one is the intrinsic rank-four condition in dimension four. -/
theorem radical_one_weights {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 1) : weight q = 6 ∨ weight q = 10 := by
  revert hr
  apply quadratic_induction hq
  intro a b c d e f g h i j k hr
  rw [radicalCard_poly] at hr
  exact (QuadraticFourRaw.all_classified a b c d e f g h i j k).1 hr

/-- Radical cardinality four is the intrinsic rank-two condition in dimension four. -/
theorem radical_four_weights {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 4) : weight q ∈ ({4,8,12} : Finset ℕ) := by
  revert hr
  apply quadratic_induction hq
  intro a b c d e f g h i j k hr
  rw [radicalCard_poly] at hr
  exact (QuadraticFourRaw.all_classified a b c d e f g h i j k).2.1 hr

/-- Every cost-two quadratic is precisely the indicator of its actual polar radical. -/
theorem cost_two_eq_radical {q : V → F₂} (hq : HasDegreeLE q 2)
    (hc : cost q = 2) : q = radicalIndicator q := by
  revert hc
  apply quadratic_induction hq
  intro a b c d e f g h i j k hc
  rw [radicalIndicator_poly]
  exact (QuadraticFourRaw.all_classified a b c d e f g h i j k).2.2 hc

theorem radicalIndicator_eq_of_polar_eq {p q : V → F₂}
    (h : ∀ x y, polar p x y = polar q x y) : radicalIndicator p = radicalIndicator q := by
  funext x
  simp only [radicalIndicator, IsRadical, h]

theorem cost_two_unique {p q : V → F₂} (hp : HasDegreeLE p 2) (hq : HasDegreeLE q 2)
    (hpolar : ∀ x y, polar p x y = polar q x y)
    (hcp : cost p = 2) (hcq : cost q = 2) : p = q := by
  rw [cost_two_eq_radical hp hcp, cost_two_eq_radical hq hcq]
  exact radicalIndicator_eq_of_polar_eq hpolar

theorem radicalIndicator_degree {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 4) : HasDegreeLE (radicalIndicator q) 2 := by
  revert hr
  apply quadratic_induction hq
  intro a b c d e f g h i j k hr
  rw [radicalCard_poly] at hr
  rw [radicalIndicator_poly, ← QuadraticFourRaw.representative_eq f g h i j k hr]
  exact poly_degree _ _ _ _ _ _ _ _ _ _ _

theorem radicalIndicator_cost {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 4) : cost (radicalIndicator q) = 2 := by
  revert hr
  apply quadratic_induction hq
  intro a b c d e f g h i j k hr
  rw [radicalCard_poly] at hr
  rw [radicalIndicator_poly, ← QuadraticFourRaw.representative_eq f g h i j k hr]
  exact QuadraticFourRaw.representative_cost f g h i j k hr

theorem radicalIndicator_polar {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 4) (x y : V) :
    polar (radicalIndicator q) x y = polar q x y := by
  revert hr
  apply quadratic_induction hq
  intro a b c d e f g h i j k hr
  rw [radicalCard_poly] at hr
  rw [radicalIndicator_poly, ← QuadraticFourRaw.representative_eq f g h i j k hr]
  change polar (poly _ _ _ _ _ f g h i j k) x y = polar (poly a b c d e f g h i j k) x y
  rw [polar_poly, polar_poly]

/-- Exactly one quadratic with this polar has cost two, and it is the radical indicator. -/
theorem exists_unique_cost_two {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 4) :
    ∃! p : V → F₂, HasDegreeLE p 2 ∧ (∀ x y, polar p x y = polar q x y) ∧ cost p = 2 := by
  refine ⟨radicalIndicator q,
    ⟨radicalIndicator_degree hq hr, radicalIndicator_polar hq hr, radicalIndicator_cost hq hr⟩, ?_⟩
  intro p hp
  exact (cost_two_eq_radical hp.1 hp.2.2).trans (radicalIndicator_eq_of_polar_eq hp.2.1)

#print axioms exists_unique_cost_two
end BooleanANF.QuadraticFour
