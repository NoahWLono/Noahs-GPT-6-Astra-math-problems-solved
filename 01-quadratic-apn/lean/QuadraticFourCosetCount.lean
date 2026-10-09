import QuadraticFourCosets
import QuadraticFourCosetCountRaw

namespace BooleanANF.QuadraticFour

/-- Distinct nonzero radical cosets, represented by their actual indicator functions. -/
def nonzeroRadicalCosets (q : V → F₂) : Finset (V → F₂) :=
  (Finset.univ.filter (fun a : V => ¬ IsRadical q a)).image
    (fun a x => radicalIndicator q (x+a))

theorem nonzeroRadicalCosets_card {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 4) : (nonzeroRadicalCosets q).card = 3 := by
  revert hr
  apply quadratic_induction hq
  intro a b c d e f g h i j k hr
  rw [radicalCard_poly] at hr
  have he : nonzeroRadicalCosets (poly a b c d e f g h i j k) =
      QuadraticFourRaw.nonzeroCosets f g h i j k := by
    simp only [nonzeroRadicalCosets, QuadraticFourRaw.nonzeroCosets,
      isRadical_poly, radicalIndicator_poly]
  rw [he]
  exact QuadraticFourRaw.nonzero_coset_count f g h i j k hr

noncomputable def costFourPerturbations (q : V → F₂) : Finset (V → F₂) := by
  classical
  exact Finset.univ.filter (fun p => HasDegreeLE p 2 ∧
    (∀ x y, polar p x y = polar q x y) ∧ cost p = 4)

theorem costFourPerturbations_eq_cosets {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 4) : costFourPerturbations q = nonzeroRadicalCosets q := by
  ext p
  simp only [costFourPerturbations, Finset.mem_filter, Finset.mem_univ, true_and,
    nonzeroRadicalCosets, Finset.mem_image]
  constructor
  · rintro ⟨hp, hpol, hcost⟩
    have hrad : radicalPoints p = radicalPoints q := by
      ext x
      simp only [radicalPoints, Finset.mem_filter, Finset.mem_univ, true_and, IsRadical, hpol]
    have hrp : (radicalPoints p).card = 4 := by rw [hrad, hr]
    obtain ⟨a,ha,he⟩ := (cost_four_iff_nonzero_coset hp hrp).mp hcost
    have hid := radicalIndicator_eq_of_polar_eq hpol
    have ha' : ¬ IsRadical q a := by simpa only [IsRadical, hpol] using ha
    refine ⟨a, ha', ?_⟩
    funext x
    rw [← hid]
    exact (he x).symm
  · rintro ⟨a,ha,rfl⟩
    exact nonzero_coset_perturbation hq hr ha

/-- Exactly three degree-two perturbations with a fixed rank-two polar have cost four. -/
theorem costFourPerturbations_card {q : V → F₂} (hq : HasDegreeLE q 2)
    (hr : (radicalPoints q).card = 4) : (costFourPerturbations q).card = 3 := by
  rw [costFourPerturbations_eq_cosets hq hr]
  exact nonzeroRadicalCosets_card hq hr

#print axioms costFourPerturbations_card
end BooleanANF.QuadraticFour
