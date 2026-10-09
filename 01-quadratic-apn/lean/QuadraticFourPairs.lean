import QuadraticFourRadical
import QuadraticFourPairEnumeration

set_option maxHeartbeats 2000000
namespace BooleanANF.QuadraticFour

theorem poly_add (a b c d e f g h i j k A B C D E F G H I J K : F₂) :
    (fun x => poly a b c d e f g h i j k x + poly A B C D E F G H I J K x) =
      poly (a+A) (b+B) (c+C) (d+D) (e+E) (f+F) (g+G) (h+H) (i+I) (j+J) (k+K) := by
  funext x
  unfold poly
  ring

/-- The pair-only rank-two pencil geometry, formulated entirely using actual
polars and actual radical indicator functions. -/
theorem pair_radical_geometry {p q : V → F₂} (hp : HasDegreeLE p 2) (hq : HasDegreeLE q 2)
    (hrp : (radicalPoints p).card = 4) (hrq : (radicalPoints q).card = 4)
    (hrpq : (radicalPoints (fun x => p x + q x)).card = 4) :
    (radicalPoints p ∩ radicalPoints q).card = 2 ∧
    ∃ x : V, radicalIndicator p x + radicalIndicator q x +
      radicalIndicator (fun y => p y + q y) x = 0 := by
  revert hrp hrq hrpq
  apply quadratic_induction hp
  intro a b c d e f g h i j k
  apply quadratic_induction hq
  intro A B C D E F G H I J K hrp hrq hrpq
  rw [poly_add] at hrpq ⊢
  rw [radicalCard_poly] at hrp hrq hrpq
  have ht := QuadraticFourRaw.all_pairs f g h i j k F G H I J K hrp hrq hrpq
  have hinter : radicalPoints (poly a b c d e f g h i j k) ∩
      radicalPoints (poly A B C D E F G H I J K) =
      Finset.univ.filter (fun x : V => QuadraticFourRaw.inRadical f g h i j k x ∧
        QuadraticFourRaw.inRadical F G H I J K x) := by
    ext x
    simp [radicalPoints, isRadical_poly]
  rw [hinter, radicalIndicator_poly, radicalIndicator_poly, radicalIndicator_poly]
  exact ht

theorem radicalIndicator_zero (q : V → F₂) : radicalIndicator q 0 = 1 := by
  have h : IsRadical q 0 := by
    intro y
    simp [polar, CharTwo.add_self_eq_zero, add_assoc, add_comm, add_left_comm]
  simp [radicalIndicator, h]

/-- The three radical indicators in a rank-two pencil never have constant sum. -/
theorem pair_radical_sum_nonconstant {p q : V → F₂}
    (hp : HasDegreeLE p 2) (hq : HasDegreeLE q 2)
    (hrp : (radicalPoints p).card = 4) (hrq : (radicalPoints q).card = 4)
    (hrpq : (radicalPoints (fun x => p x + q x)).card = 4) :
    ¬ ∃ c : F₂, ∀ x : V, radicalIndicator p x + radicalIndicator q x +
      radicalIndicator (fun y => p y + q y) x = c := by
  obtain ⟨_,x,hx⟩ := pair_radical_geometry hp hq hrp hrq hrpq
  rintro ⟨c,hc⟩
  have h0 := hc 0
  rw [radicalIndicator_zero, radicalIndicator_zero, radicalIndicator_zero] at h0
  have hh : (0 : F₂) = 1 := by
    calc
      0 = c := hx.symm.trans (hc x)
      _ = 1 := by simpa using h0.symm
  exact zero_ne_one hh

#print axioms pair_radical_geometry
#print axioms pair_radical_sum_nonconstant
end BooleanANF.QuadraticFour
