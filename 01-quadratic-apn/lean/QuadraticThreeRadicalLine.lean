import QuadraticFourPolar
import WeightThirtyTypeB

namespace BooleanANF.QuadraticFour

/-- In three dimensions the radical vector is the reverse list of independent
alternating-matrix entries. This is a symbolic identity, not a pencil lookup. -/
theorem three_alternating_kernel (a b c u v w : F₂)
    (hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (a*v+b*w=0 ∧ a*u+c*w=0 ∧ b*u+c*v=0) ↔
    ((u=0 ∧ v=0 ∧ w=0) ∨ (u=c ∧ v=b ∧ w=a)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases u <;> fin_cases v <;> fin_cases w <;>
      norm_num [show (2 : F₂) = 0 from rfl] at hn ⊢
  all_goals rfl

/-- The actual polar radical of a four-variable form independent of the last
coordinate is the lift of that radical line, uniformly for all coefficients. -/
theorem radical_three_coordinates (a b c d e f g i : F₂)
    (hn : f ≠ 0 ∨ g ≠ 0 ∨ i ≠ 0) (x : V) :
    IsRadical (poly a b c d e f g 0 i 0 0) x ↔
      ((x 0=0 ∧ x 1=0 ∧ x 2=0) ∨ (x 0=i ∧ x 1=g ∧ x 2=f)) := by
  rw [isRadical_poly]
  simp only [QuadraticFourRaw.inRadical, zero_mul, add_zero, zero_add, and_true]
  exact three_alternating_kernel f g i (x 0) (x 1) (x 2) hn

end BooleanANF.QuadraticFour
