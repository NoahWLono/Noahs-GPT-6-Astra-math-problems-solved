import QuadraticFourCertificates
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace BooleanANF.QuadraticFour

/-- Explicit polynomial in the canonical order constant, linears, quadratics. -/
def poly (a b c d e f g h i j k : F₂) (x : V) : F₂ :=
  a + b*x 0 + c*x 1 + d*x 2 + e*x 3 + f*x 0*x 1 +
    g*x 0*x 2 + h*x 0*x 3 + i*x 1*x 2 + j*x 1*x 3 + k*x 2*x 3

theorem eval_eq_poly (c : Coeff) :
    eval c = poly (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)
      (c 6) (c 7) (c 8) (c 9) (c 10) := by
  funext x
  simp [eval, Fin.sum_univ_succ, indices, monomial_eq_prod, poly]
  ring


end BooleanANF.QuadraticFour
