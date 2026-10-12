module
public import ZariskiOriginal
public import ZariskiComplexClosure
public import ZariskiPolynomiality

@[expose] public section
noncomputable section
namespace ZariskiCylinder
open Polynomial

/-- Checked complex pointwise transitivity for the exact adapted hypersurface. -/
theorem complex_transitive_thirteen (P : ℂ[X]) (hP : P.natDegree ≠ 0)
    (p q : Point ℂ) (hp : equation P p = 0) (hq : equation P q = 0) :
    Reaches P 13 p q := transitive_thirteen P hP p q hp hq

/-- Checked statement on the original cylinder, via the checked polynomial change of coordinates. -/
theorem complex_original_transitive_thirteen (P : ℂ[X]) (hP : P.natDegree ≠ 0)
    (p q : Point ℂ) (hp : originalEquation P p = 0) (hq : originalEquation P q = 0) :
    OriginalReaches P 13 p q := original_transitive_thirteen P hP p q hp hq

/-- Polynomiality of each of the four actual parameterized maps, including all exceptional loci. -/
theorem four_polynomial_actions (P : ℂ[X]) :
    IsPolynomialAction (tau (k := ℂ)) ∧
    IsPolynomialAction (deltaZ (k := ℂ)) ∧
    IsPolynomialAction (deltaT P) ∧ IsPolynomialAction (extra P) :=
  ⟨polynomial_tau, polynomial_deltaZ, polynomial_deltaT P, polynomial_extra P⟩

#print axioms complex_transitive_thirteen
#print axioms complex_original_transitive_thirteen
#print axioms four_polynomial_actions
end ZariskiCylinder
