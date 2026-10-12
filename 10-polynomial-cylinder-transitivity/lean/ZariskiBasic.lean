module
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Tactic.Ring

/-!
Explicit polynomial identities for cylinders over x² y + z² + x + P(t) = 0.
The scaled fourth action extends Poloni's 2026 cubic formulas. This module
proves identities only. Transitivity and prior-art status are separate claims.
-/
@[expose] public section

noncomputable section
namespace ZariskiCylinder

@[ext] structure Point (k : Type*) where
  x : k
  y : k
  z : k
  t : k
  u : k

variable {k : Type*} [CommRing k]

def av (p : Point k) : k := 1 + p.x * p.y + 2 * p.z * p.u
def cv (p : Point k) : k := p.z * p.y - 2 * av p * p.u
def mv (p : Point k) : k := p.z * p.y + 2 * av p * p.u

def equation (P : Polynomial k) (p : Point k) : k :=
  p.x ^ 2 * p.y + 2 * p.x * p.z * p.u + p.z ^ 2 + p.x + P.eval p.t

theorem equation_av (P : Polynomial k) (p : Point k) :
    equation P p = av p * p.x + p.z ^ 2 + P.eval p.t := by
  unfold equation av
  ring

theorem mv_add_cv (p : Point k) : mv p + cv p = 2 * p.z * p.y := by
  unfold mv cv
  ring

/-- Universal two-parameter polynomial step, before imposing the divided-difference law. -/
def eStep (p : Point k) (s h : k) : Point k where
  x := p.x + 2 * mv p * h - 4 * av p * p.y ^ 2 * h ^ 2
  y := p.y
  z := p.z - 2 * av p * p.y * h
  t := p.t + 2 * av p * cv p * s
  u := p.u - p.y ^ 2 * h

@[simp] theorem eStep_x (p : Point k) (s h : k) :
    (eStep p s h).x = p.x + 2 * mv p * h - 4 * av p * p.y ^ 2 * h ^ 2 := rfl
@[simp] theorem eStep_y (p : Point k) (s h : k) : (eStep p s h).y = p.y := rfl
@[simp] theorem eStep_z (p : Point k) (s h : k) :
    (eStep p s h).z = p.z - 2 * av p * p.y * h := rfl
@[simp] theorem eStep_t (p : Point k) (s h : k) :
    (eStep p s h).t = p.t + 2 * av p * cv p * s := rfl
@[simp] theorem eStep_u (p : Point k) (s h : k) :
    (eStep p s h).u = p.u - p.y ^ 2 * h := rfl

@[simp] theorem av_eStep (p : Point k) (s h : k) : av (eStep p s h) = av p := by
  simp only [av, eStep, mv]
  ring

@[simp] theorem cv_eStep (p : Point k) (s h : k) : cv (eStep p s h) = cv p := by
  simp only [cv, av_eStep]
  simp only [eStep]
  ring

@[simp] theorem mv_eStep (p : Point k) (s h : k) :
    mv (eStep p s h) = mv p - 4 * av p * p.y ^ 2 * h := by
  simp only [mv, av_eStep]
  simp only [eStep]
  ring

@[simp] theorem eStep_zero (p : Point k) : eStep p 0 0 = p := by
  ext <;> simp [eStep]

theorem eStep_add (p : Point k) (s h r j : k) :
    eStep (eStep p s h) r j = eStep p (s + r) (h + j) := by
  ext <;> simp only [eStep_x, eStep_y, eStep_z, eStep_t, eStep_u,
    av_eStep, cv_eStep, mv_eStep] <;> ring

theorem equation_eStep (P : Polynomial k) (p : Point k) (s h : k)
    (hh : P.eval (p.t + 2 * av p * cv p * s) - P.eval p.t =
      2 * av p * cv p * h) :
    equation P (eStep p s h) = equation P p := by
  rw [equation_av, av_eStep, equation_av]
  simp only [eStep]
  have hP : P.eval (p.t + 2 * av p * cv p * s) =
      P.eval p.t + 2 * av p * cv p * h := by rw [← hh]; ring
  rw [hP]
  unfold mv cv
  ring

def tau (p : Point k) (s : k) : Point k where
  x := p.x
  y := p.y + 2 * s * p.u + s ^ 2
  z := p.z - s * p.x
  t := p.t
  u := p.u + s

@[simp] theorem equation_tau (P : Polynomial k) (p : Point k) (s : k) :
    equation P (tau p s) = equation P p := by
  simp only [equation, tau]
  ring

@[simp] theorem tau_zero (p : Point k) : tau p 0 = p := by ext <;> simp [tau]

theorem tau_add (p : Point k) (s r : k) : tau (tau p s) r = tau p (s + r) := by
  ext <;> simp only [tau] <;> ring

def deltaZ (p : Point k) (s : k) : Point k where
  x := p.x
  y := p.y - 2 * s * (p.z + p.x * p.u) - s ^ 2 * p.x ^ 2
  z := p.z + s * p.x ^ 2
  t := p.t
  u := p.u

@[simp] theorem equation_deltaZ (P : Polynomial k) (p : Point k) (s : k) :
    equation P (deltaZ p s) = equation P p := by
  simp only [equation, deltaZ]
  ring

@[simp] theorem deltaZ_zero (p : Point k) : deltaZ p 0 = p := by ext <;> simp [deltaZ]

theorem deltaZ_add (p : Point k) (s r : k) :
    deltaZ (deltaZ p s) r = deltaZ p (s + r) := by
  ext <;> simp only [deltaZ] <;> ring

def tStep (p : Point k) (s h : k) : Point k where
  x := p.x
  y := p.y - h
  z := p.z
  t := p.t + s * p.x ^ 2
  u := p.u

@[simp] theorem tStep_zero (p : Point k) : tStep p 0 0 = p := by ext <;> simp [tStep]

theorem tStep_add (p : Point k) (s h r j : k) :
    tStep (tStep p s h) r j = tStep p (s + r) (h + j) := by
  ext <;> simp only [tStep] <;> ring

theorem equation_tStep (P : Polynomial k) (p : Point k) (s h : k)
    (hh : P.eval (p.t + s * p.x ^ 2) - P.eval p.t = p.x ^ 2 * h) :
    equation P (tStep p s h) = equation P p := by
  have hP : P.eval (p.t + s * p.x ^ 2) = P.eval p.t + p.x ^ 2 * h := by
    rw [← hh]; ring
  simp only [equation, tStep]
  rw [hP]
  ring

#print axioms eStep_add
#print axioms equation_eStep
end ZariskiCylinder
