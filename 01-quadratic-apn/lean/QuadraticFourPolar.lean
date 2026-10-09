import QuadraticFourPolynomial
import QuadraticFourRadicalRaw

namespace BooleanANF.QuadraticFour
open scoped BigOperators

def polar (q : V → F₂) (x y : V) : F₂ := q (x+y) + q x + q y + q 0

def IsRadical (q : V → F₂) (x : V) : Prop := ∀ y, polar q x y = 0

instance (q : V → F₂) (x : V) : Decidable (IsRadical q x) :=
  inferInstanceAs (Decidable (∀ y, polar q x y = 0))

def radicalPoints (q : V → F₂) : Finset V := Finset.univ.filter (IsRadical q)

def radicalIndicator (q : V → F₂) (x : V) : F₂ := if IsRadical q x then 1 else 0

/-- The normalized polar is the actual alternating bilinear expression of the
six quadratic coefficients; affine perturbations disappear. -/
theorem polar_poly (a b c d e f g h i j k : F₂) (x y : V) :
    polar (poly a b c d e f g h i j k) x y =
      (f*x 1 + g*x 2 + h*x 3)*y 0 +
      (f*x 0 + i*x 2 + j*x 3)*y 1 +
      (g*x 0 + i*x 1 + k*x 3)*y 2 +
      (h*x 0 + j*x 1 + k*x 2)*y 3 := by
  simp [polar, poly, Pi.add_apply, Pi.zero_apply]
  ring_nf
  simp only [show (2 : F₂) = 0 from rfl, show (4 : F₂) = 0 from rfl, mul_zero, add_zero, zero_add]

theorem isRadical_poly (a b c d e f g h i j k : F₂) (x : V) :
    IsRadical (poly a b c d e f g h i j k) x ↔ QuadraticFourRaw.inRadical f g h i j k x := by
  constructor
  · intro H
    have h0 := H ![1,0,0,0]
    have h1 := H ![0,1,0,0]
    have h2 := H ![0,0,1,0]
    have h3 := H ![0,0,0,1]
    simp only [polar_poly] at h0 h1 h2 h3
    exact ⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3⟩
  · rintro ⟨h0,h1,h2,h3⟩ y
    rw [polar_poly, h0, h1, h2, h3]
    simp

theorem radicalIndicator_poly (a b c d e f g h i j k : F₂) :
    radicalIndicator (poly a b c d e f g h i j k) =
      QuadraticFourRaw.radicalIndicator f g h i j k := by
  funext x
  simp only [radicalIndicator, QuadraticFourRaw.radicalIndicator, isRadical_poly]

theorem radicalCard_poly (a b c d e f g h i j k : F₂) :
    (radicalPoints (poly a b c d e f g h i j k)).card =
      QuadraticFourRaw.radicalCard f g h i j k := by
  change _ = weight (QuadraticFourRaw.radicalIndicator f g h i j k)
  rw [weight_eq_support_card]
  congr 1
  ext x
  simp [radicalPoints, isRadical_poly, QuadraticFourRaw.radicalIndicator]

end BooleanANF.QuadraticFour
