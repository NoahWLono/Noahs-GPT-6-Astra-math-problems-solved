import Mathlib.Tactic.Ring

/-! Universal polynomial equalities from ASTRA-01 Section 4 and Section 5.3.
No finite-field sampling, denominator cancellation, or cryptographic solver.
The identities alone do not certify the geometric interpretation or degree. -/
namespace Astra01
variable {K : Type*} [CommRing K]

def cubic (a b x : K) : K := x^3 + a*x + b
def delta (x u : K) : K := (x-u)^2
def middle (a b x u : K) : K := (x+u)*(x*u+a)+2*b
def semaev3 (a b x u z : K) : K :=
  delta x u * z^2 - 2*middle a b x u*z + (x*u-a)^2-4*b*(x+u)

/-- The manuscript's exact Semaev factorization over any commutative ring. -/
theorem semaev_factorization (a b x u z : K) :
    (delta x u*z-middle a b x u)^2 - 4*cubic a b u*cubic a b x =
      delta x u * semaev3 a b x u z := by
  unfold semaev3 delta middle cubic
  ring

/-- Denominator-cleared addition numerator, assuming both curve equations. -/
theorem addition_numerator (a b x y u v : K)
    (hy : y^2 = cubic a b x) (hv : v^2 = cubic a b u) :
    (y-v)^2 - (x+u)*delta x u = middle a b x u - 2*v*y := by
  calc
    (y-v)^2 - (x+u)*delta x u =
        y^2 + v^2 - 2*v*y - (x+u)*delta x u := by ring
    _ = cubic a b x + cubic a b u - 2*v*y - (x+u)*delta x u := by rw [hy,hv]
    _ = middle a b x u - 2*v*y := by unfold cubic delta middle; ring

/-- Numerator used by the usual x-only doubling expression. -/
theorem duplication_numerator (a b x : K) :
    (3*x^2+a)^2 - 8*x*cubic a b x = x^4-2*a*x^2-8*b*x+a^2 := by
  unfold cubic
  ring

#print axioms semaev_factorization
#print axioms addition_numerator
#print axioms duplication_numerator
end Astra01
