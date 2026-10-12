module
public import ZariskiMain

@[expose] public section
noncomputable section
namespace ZariskiCylinder.Expected
open Polynomial

/-- Independent explicit specification of the formal outcome. The only
polynomial hypothesis is nonconstancy; no surjectivity or bridge is assumed. -/
def FullStatement : Prop :=
  ∀ (P : ℂ[X]), P.natDegree ≠ 0 →
    IsPolynomialAction (tau (k := ℂ)) ∧
    IsPolynomialAction (deltaZ (k := ℂ)) ∧
    IsPolynomialAction (deltaT P) ∧
    IsPolynomialAction (extra P) ∧
    (∀ (p : Point ℂ) (s r : ℂ), tau (tau p s) r = tau p (s + r)) ∧
    (∀ (p : Point ℂ) (s r : ℂ), deltaZ (deltaZ p s) r = deltaZ p (s + r)) ∧
    (∀ (p : Point ℂ) (s r : ℂ), deltaT P (deltaT P p s) r = deltaT P p (s + r)) ∧
    (∀ (p : Point ℂ) (s r : ℂ), extra P (extra P p s) r = extra P p (s + r)) ∧
    (∀ (p : Point ℂ) (s : ℂ), equation P (tau p s) = equation P p) ∧
    (∀ (p : Point ℂ) (s : ℂ), equation P (deltaZ p s) = equation P p) ∧
    (∀ (p : Point ℂ) (s : ℂ), equation P (deltaT P p s) = equation P p) ∧
    (∀ (p : Point ℂ) (s : ℂ), equation P (extra P p s) = equation P p) ∧
    (∀ (p q : Point ℂ),
      p.x ^ 2 * p.y + p.z ^ 2 + p.x + P.eval p.t = 0 →
      q.x ^ 2 * q.y + q.z ^ 2 + q.x + P.eval q.t = 0 →
      OriginalReaches P 13 p q)

theorem checked_main : FullStatement := by
  intro P hP
  exact ⟨polynomial_tau, polynomial_deltaZ, polynomial_deltaT P, polynomial_extra P,
    tau_add, deltaZ_add, deltaT_add P, extra_add P,
    equation_tau P, equation_deltaZ P, equation_deltaT P, equation_extra P,
    complex_original_transitive_thirteen P hP⟩

#print axioms checked_main
end ZariskiCylinder.Expected
