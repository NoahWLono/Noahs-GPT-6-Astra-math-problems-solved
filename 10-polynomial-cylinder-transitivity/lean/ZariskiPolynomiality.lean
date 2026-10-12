module
public import ZariskiActions
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section
noncomputable section
namespace ZariskiCylinder
open Polynomial

section Naturality
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The same formula as difference, generalized to arbitrary coefficient rings. -/
def rawDifference (P : R[X]) (t q s : R) : R :=
  s * (P.comp (X + C t)).divX.eval (q * s)

theorem map_divX (f : R →+* S) (P : R[X]) :
    P.divX.map f = (P.map f).divX := by
  ext n
  simp [coeff_divX]

theorem rawDifference_map (f : R →+* S) (P : R[X]) (t q s : R) :
    f (rawDifference P t q s) = rawDifference (P.map f) (f t) (f q) (f s) := by
  have hd : ((P.comp (X + C t)).divX).map f =
      ((P.map f).comp (X + C (f t))).divX := by
    rw [map_divX, Polynomial.map_comp]
    simp
  unfold rawDifference
  rw [map_mul, ← Polynomial.eval_map_apply, hd, map_mul]

def pointMap (f : R →+* S) (p : Point R) : Point S :=
  ⟨f p.x, f p.y, f p.z, f p.t, f p.u⟩

@[simp] theorem pointMap_eStep (f : R →+* S) (p : Point R) (s h : R) :
    pointMap f (eStep p s h) = eStep (pointMap f p) (f s) (f h) := by
  ext <;> simp [map_ofNat, pointMap, eStep, av, cv, mv]

@[simp] theorem pointMap_tau (f : R →+* S) (p : Point R) (s : R) :
    pointMap f (tau p s) = tau (pointMap f p) (f s) := by
  ext <;> simp [map_ofNat, pointMap, tau]

@[simp] theorem pointMap_deltaZ (f : R →+* S) (p : Point R) (s : R) :
    pointMap f (deltaZ p s) = deltaZ (pointMap f p) (f s) := by
  ext <;> simp [map_ofNat, pointMap, deltaZ]

@[simp] theorem pointMap_tStep (f : R →+* S) (p : Point R) (s h : R) :
    pointMap f (tStep p s h) = tStep (pointMap f p) (f s) (f h) := by
  ext <;> simp [map_ofNat, pointMap, tStep]

def rawExtra (P : R[X]) (p : Point R) (s : R) : Point R :=
  eStep p s (rawDifference P p.t (2 * av p * cv p) s)

def rawDeltaT (P : R[X]) (p : Point R) (s : R) : Point R :=
  tStep p s (rawDifference P p.t (p.x ^ 2) s)

@[simp] theorem pointMap_rawExtra (f : R →+* S) (P : R[X]) (p : Point R) (s : R) :
    pointMap f (rawExtra P p s) = rawExtra (P.map f) (pointMap f p) (f s) := by
  simp only [rawExtra, pointMap_eStep, rawDifference_map]
  simp [map_ofNat, av, cv, pointMap]

@[simp] theorem pointMap_rawDeltaT (f : R →+* S) (P : R[X]) (p : Point R) (s : R) :
    pointMap f (rawDeltaT P p s) = rawDeltaT (P.map f) (pointMap f p) (f s) := by
  simp only [rawDeltaT, pointMap_tStep, rawDifference_map]
  simp [pointMap]
end Naturality

section Polynomiality
variable {k : Type*} [Field k]

/-- All six variables, including the additive-group parameter, are polynomial coordinates. -/
def IsPolynomialAction (F : Point k → k → Point k) : Prop :=
  ∃ G : Point (MvPolynomial (Fin 6) k), ∀ ρ : Fin 6 → k,
    pointMap (MvPolynomial.eval₂Hom (RingHom.id k) ρ) G =
      F ⟨ρ 0, ρ 1, ρ 2, ρ 3, ρ 4⟩ (ρ 5)

def universalPoint : Point (MvPolynomial (Fin 6) k) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
   MvPolynomial.X 3, MvPolynomial.X 4⟩

@[simp] theorem eval_universalPoint (ρ : Fin 6 → k) :
    pointMap (MvPolynomial.eval₂Hom (RingHom.id k) ρ) universalPoint =
      ⟨ρ 0, ρ 1, ρ 2, ρ 3, ρ 4⟩ := by
  ext <;> simp [universalPoint, pointMap]

@[simp] theorem map_eval_coefficients (P : k[X]) (ρ : Fin 6 → k) :
    (P.map MvPolynomial.C).map (MvPolynomial.eval₂Hom (RingHom.id k) ρ) = P := by
  rw [Polynomial.map_map]
  have hf : (MvPolynomial.eval₂Hom (RingHom.id k) ρ).comp MvPolynomial.C = RingHom.id k := by
    ext r
    simp
  rw [hf, Polynomial.map_id]

theorem polynomial_tau : IsPolynomialAction (tau (k := k)) := by
  refine ⟨tau universalPoint (MvPolynomial.X 5), ?_⟩
  intro ρ
  simp

theorem polynomial_deltaZ : IsPolynomialAction (deltaZ (k := k)) := by
  refine ⟨deltaZ universalPoint (MvPolynomial.X 5), ?_⟩
  intro ρ
  simp

theorem polynomial_deltaT (P : k[X]) : IsPolynomialAction (deltaT P) := by
  refine ⟨rawDeltaT (P.map MvPolynomial.C) universalPoint (MvPolynomial.X 5), ?_⟩
  intro ρ
  simp only [pointMap_rawDeltaT, map_eval_coefficients, eval_universalPoint]
  simp [rawDeltaT, deltaT, rawDifference, difference, divided]

theorem polynomial_extra (P : k[X]) : IsPolynomialAction (extra P) := by
  refine ⟨rawExtra (P.map MvPolynomial.C) universalPoint (MvPolynomial.X 5), ?_⟩
  intro ρ
  simp only [pointMap_rawExtra, map_eval_coefficients, eval_universalPoint]
  simp [rawExtra, extra, rawDifference, difference, divided]

#print axioms polynomial_extra
end Polynomiality
end ZariskiCylinder
