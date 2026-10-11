import Mathlib.Data.Finsupp.Multiset
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Valuation

/-! A concrete divisor on the projective line, represented by its finite
coefficients and its coefficient at infinity. This is not yet a divisor
on the elliptic source curve. `intDegree` is used only for order at infinity,
never as the degree of a rational morphism. -/
namespace Astra01.RationalFunctionDivisor
noncomputable section
open Polynomial
open scoped RatFunc
variable {K : Type*} [Field K]
local instance : DecidableEq K⟮X⟯ := Classical.decEq _

/-- Finite root divisor, with the actual polynomial root multiplicities. -/
def rootDivisor (p : K[X]) : K →₀ ℤ := by
  classical
  exact p.roots.toFinsupp.mapRange (fun n : ℕ => (n : ℤ)) (by rfl)

@[simp] theorem rootDivisor_apply (p : K[X]) (a : K) :
    rootDivisor p a = (p.rootMultiplicity a : ℤ) := by
  classical
  simp [rootDivisor, Polynomial.count_roots]

/-- A divisor in the finite-affine-chart plus one infinity-point presentation. -/
abbrev Divisor (K : Type*) := (K →₀ ℤ) × ℤ

def degree (D : Divisor K) : ℤ := D.1.sum (fun _ n => n) + D.2

/-- The usual numerator/denominator divisor; totalized to zero at f = 0. -/
def principalDivisor (f : K⟮X⟯) : Divisor K :=
  (rootDivisor f.num - rootDivisor f.denom, -f.intDegree)

@[simp] theorem principalDivisor_finite (f : K⟮X⟯) (a : K) :
    (principalDivisor f).1 a = (f.num.rootMultiplicity a : ℤ) -
      (f.denom.rootMultiplicity a : ℤ) := by
  simp [principalDivisor]

/-- The infinity coefficient is the negative logarithmic valuation exponent. -/
theorem principalDivisor_infinity_valuation (f : K⟮X⟯) (hf : f ≠ 0) :
    RatFunc.inftyValuation K f = WithZero.exp (-(principalDivisor f).2) := by
  simp [principalDivisor, RatFunc.inftyValuation_apply, RatFunc.inftyValuationDef, hf]

theorem rootDivisor_sum [IsAlgClosed K] (p : K[X]) :
    (rootDivisor p).sum (fun _ n => n) = (p.natDegree : ℤ) := by
  classical
  unfold rootDivisor
  rw [Finsupp.sum_mapRange_index (fun _ => (rfl : (0 : ℤ) = 0))]
  have h := congrArg (fun n : ℕ => (n : ℤ)) p.roots.toFinsupp_sum_eq
  simpa only [Finsupp.sum, Nat.cast_sum, id_eq, IsAlgClosed.card_roots_eq_natDegree] using h

/-- The full principal divisor, including infinity, has degree zero. -/
theorem principalDivisor_degree_zero [IsAlgClosed K] (f : K⟮X⟯) (_hf : f ≠ 0) :
    degree (principalDivisor f) = 0 := by
  classical
  simp [degree, principalDivisor, Finsupp.sum_sub_index, rootDivisor_sum,
    RatFunc.intDegree]

#print axioms principalDivisor_degree_zero
#print axioms principalDivisor_finite
#print axioms principalDivisor_infinity_valuation
end
end Astra01.RationalFunctionDivisor
