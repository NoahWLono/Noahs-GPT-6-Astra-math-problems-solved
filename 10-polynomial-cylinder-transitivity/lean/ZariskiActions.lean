module
public import ZariskiDifference

@[expose] public section

noncomputable section
namespace ZariskiCylinder
open Polynomial
variable {k : Type*} [Field k]

def extra (P : k[X]) (p : Point k) (s : k) : Point k :=
  eStep p s (difference P p.t (2 * av p * cv p) s)

def deltaT (P : k[X]) (p : Point k) (s : k) : Point k :=
  tStep p s (difference P p.t (p.x ^ 2) s)

@[simp] theorem av_extra (P : k[X]) (p : Point k) (s : k) : av (extra P p s) = av p := by
  simp [extra]
@[simp] theorem cv_extra (P : k[X]) (p : Point k) (s : k) : cv (extra P p s) = cv p := by
  simp [extra]
@[simp] theorem extra_t (P : k[X]) (p : Point k) (s : k) :
    (extra P p s).t = p.t + 2 * av p * cv p * s := rfl

@[simp] theorem extra_zero (P : k[X]) (p : Point k) : extra P p 0 = p := by
  simp [extra]

@[simp] theorem equation_extra (P : k[X]) (p : Point k) (s : k) :
    equation P (extra P p s) = equation P p := by
  apply equation_eStep
  exact difference_mul P p.t (2 * av p * cv p) s

theorem extra_add (P : k[X]) (p : Point k) (s r : k) :
    extra P (extra P p s) r = extra P p (s + r) := by
  unfold extra
  simp only [eStep_t, av_eStep, cv_eStep]
  rw [eStep_add, difference_add]

@[simp] theorem deltaT_x (P : k[X]) (p : Point k) (s : k) : (deltaT P p s).x = p.x := rfl
@[simp] theorem deltaT_t (P : k[X]) (p : Point k) (s : k) :
    (deltaT P p s).t = p.t + s * p.x ^ 2 := rfl

@[simp] theorem deltaT_zero (P : k[X]) (p : Point k) : deltaT P p 0 = p := by
  simp [deltaT]

@[simp] theorem equation_deltaT (P : k[X]) (p : Point k) (s : k) :
    equation P (deltaT P p s) = equation P p := by
  apply equation_tStep
  simpa only [mul_comm s (p.x ^ 2)] using difference_mul P p.t (p.x ^ 2) s

theorem deltaT_add (P : k[X]) (p : Point k) (s r : k) :
    deltaT P (deltaT P p s) r = deltaT P p (s + r) := by
  unfold deltaT
  change tStep (tStep p s (difference P p.t (p.x ^ 2) s)) r
    (difference P (p.t + s * p.x ^ 2) (p.x ^ 2) r) =
    tStep p (s + r) (difference P p.t (p.x ^ 2) (s + r))
  rw [tStep_add, difference_add]
  rw [mul_comm s (p.x ^ 2)]

/-- The exact four permitted generators. -/
inductive Move (P : k[X]) : Point k → Point k → Prop
  | tau (p : Point k) (s : k) : Move P p (ZariskiCylinder.tau p s)
  | deltaZ (p : Point k) (s : k) : Move P p (ZariskiCylinder.deltaZ p s)
  | deltaT (p : Point k) (s : k) : Move P p (ZariskiCylinder.deltaT P p s)
  | extra (p : Point k) (s : k) : Move P p (ZariskiCylinder.extra P p s)

/-- A word of at most n of the explicitly defined polynomial generators. -/
inductive Reaches (P : k[X]) : ℕ → Point k → Point k → Prop
  | refl (p : Point k) : Reaches P 0 p p
  | step {n : ℕ} {p q r : Point k} :
      Reaches P n p q → Move P q r → Reaches P (n + 1) p r
  | pad {n : ℕ} {p q : Point k} : Reaches P n p q → Reaches P (n + 1) p q

namespace Move
variable {P : k[X]} {p q : Point k}

theorem symm (h : Move P p q) : Move P q p := by
  cases h with
  | tau s => simpa only [tau_add, add_neg_cancel, tau_zero] using Move.tau (P := P) (ZariskiCylinder.tau p s) (-s)
  | deltaZ s => simpa only [deltaZ_add, add_neg_cancel, deltaZ_zero] using Move.deltaZ (P := P) (ZariskiCylinder.deltaZ p s) (-s)
  | deltaT s => simpa only [deltaT_add, add_neg_cancel, deltaT_zero] using Move.deltaT (P := P) (ZariskiCylinder.deltaT P p s) (-s)
  | extra s => simpa only [extra_add, add_neg_cancel, extra_zero] using Move.extra (P := P) (ZariskiCylinder.extra P p s) (-s)

theorem preserves (h : Move P p q) : equation P q = equation P p := by
  cases h <;> simp
end Move

namespace Reaches
variable {P : k[X]} {p q r : Point k} {n m : ℕ}

theorem single (h : Move P p q) : Reaches P 1 p q := .step (.refl p) h

theorem trans (hpq : Reaches P n p q) (hqr : Reaches P m q r) :
    Reaches P (n + m) p r := by
  induction hqr with
  | refl => simpa using hpq
  | step h₁ h₂ ih => exact .step (ih hpq) h₂
  | pad h ih => exact .pad (ih hpq)

theorem symm (h : Reaches P n p q) : Reaches P n q p := by
  induction h with
  | refl p => exact .refl p
  | step h hmove ih =>
      have hh := (single hmove.symm).trans ih
      simpa only [Nat.add_comm 1] using hh
  | pad h ih => exact .pad ih

theorem preserves (h : Reaches P n p q) : equation P q = equation P p := by
  induction h with
  | refl => rfl
  | step h hmove ih => exact hmove.preserves.trans ih
  | pad h ih => exact ih
end Reaches

#print axioms extra_add
#print axioms Reaches.symm
end ZariskiCylinder
