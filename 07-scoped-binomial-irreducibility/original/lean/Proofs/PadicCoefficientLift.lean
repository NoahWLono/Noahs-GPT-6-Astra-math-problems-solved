import LocalCoefficientNonsplit
import LocalCoefficientSplit
import PadicUnitDichotomy

/-! The unit-parameter p-local polynomial and coefficient lift, assembled from
actual translated-Eisenstein and actual split local equations. -/
set_option autoImplicit false
open Polynomial
namespace PillaiLocalCoefficients
universe u

/-- For a p-adic unit parameter, the rational polynomial from the actual affine
prime-power equation has a reduced integral polynomial lift at p. -/
theorem padic_polynomial_lift_of_power_equation
    (p q : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p)
    (hq : q.Prime) (hpq : p < q)
    (k A : ℤ) (hk : ¬ (p : ℤ) ∣ k)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ) :
    ∃ P : ℤ_[p][X], P.natDegree < p ∧
      P.map (algebraMap ℤ_[p] ℚ_[p]) = G.map (algebraMap ℚ ℚ_[p]) := by
  rcases PillaiPadic.padic_unit_dichotomy (p := p) hp3 k k hk rfl with he | ⟨b, hb, hu⟩
  · exact padic_polynomial_lift_of_translated_eisenstein p q hq.pos k A
      θ hθ hirr G hG heq he
  · exact split_integral_polynomial_lift p q hq hpq k A θ hθ hirr G hG heq b hb hu

/-- Exact p-local coefficient endpoint: no local integrality, coordinate,
minimal-polynomial, degree, or maximal-order bridge is assumed. -/
theorem padic_coefficients_of_power_equation
    (p q : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p)
    (hq : q.Prime) (hpq : p < q)
    (k A : ℤ) (hk : ¬ (p : ℤ) ∣ k)
    {L : Type u} [Field L] [Algebra ℚ L]
    (θ : L) (hθ : θ ^ p = (k : L))
    (hirr : Irreducible ((X : ℚ[X]) ^ p - C (k : ℚ)))
    (G : ℚ[X]) (hG : G.natDegree < p)
    (heq : (aeval θ G) ^ q = (A : L) - θ) :
    ∀ j : ℕ, ∃ a : ℤ_[p],
      algebraMap ℤ_[p] ℚ_[p] a = (G.coeff j : ℚ_[p]) := by
  obtain ⟨P, _, hP⟩ := padic_polynomial_lift_of_power_equation p q hp3 hq hpq k A hk
    θ hθ hirr G hG heq
  intro j
  refine ⟨P.coeff j, ?_⟩
  have hc := congrArg (fun Q : ℚ_[p][X] => Q.coeff j) hP
  simpa only [coeff_map, eq_ratCast] using hc

end PillaiLocalCoefficients
