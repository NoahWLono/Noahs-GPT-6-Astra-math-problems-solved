import QuadraticFourRaw

namespace QuadraticFourRaw
open scoped BigOperators

/-- The four rows of the actual alternating polar matrix. -/
def inRadical (f g h i j k : F) (x : V) : Prop :=
  f*x 1 + g*x 2 + h*x 3 = 0 ∧
  f*x 0 + i*x 2 + j*x 3 = 0 ∧
  g*x 0 + i*x 1 + k*x 3 = 0 ∧
  h*x 0 + j*x 1 + k*x 2 = 0

instance (f g h i j k : F) (x : V) : Decidable (inRadical f g h i j k x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def radicalIndicator (f g h i j k : F) (x : V) : F :=
  if inRadical f g h i j k x then 1 else 0

def radicalCard (f g h i j k : F) : ℕ := weight (radicalIndicator f g h i j k)

def cost (q : V → F) : ℤ := (weight q : ℤ) - 2 * ((q 0).val : ℤ)

/-- Finite statement subsequently transported to canonical degree-two functions. -/
def classified (a b c d e f g h i j k : F) : Prop :=
  (radicalCard f g h i j k = 1 → weight (poly a b c d e f g h i j k) = 6 ∨
      weight (poly a b c d e f g h i j k) = 10) ∧
  (radicalCard f g h i j k = 4 → weight (poly a b c d e f g h i j k) ∈ ({4,8,12} : Finset ℕ)) ∧
  (cost (poly a b c d e f g h i j k) = 2 →
    poly a b c d e f g h i j k = radicalIndicator f g h i j k)

instance (a b c d e f g h i j k : F) : Decidable (classified a b c d e f g h i j k) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end QuadraticFourRaw
