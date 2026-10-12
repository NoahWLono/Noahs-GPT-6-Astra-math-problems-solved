module
public import ZariskiTransitivity

@[expose] public section

noncomputable section
namespace ZariskiCylinder
open Polynomial
variable {k : Type*} [Field k] [CharZero k]

def originalEquation (P : k[X]) (p : Point k) : k :=
  p.x ^ 2 * p.y + p.z ^ 2 + p.x + P.eval p.t

def adapt (p : Point k) : Point k :=
  ⟨p.x, p.y + p.u ^ 2, p.z - p.x * p.u, p.t, p.u⟩
def unadapt (p : Point k) : Point k :=
  ⟨p.x, p.y - p.u ^ 2, p.z + p.x * p.u, p.t, p.u⟩

@[simp] theorem unadapt_adapt (p : Point k) : unadapt (adapt p) = p := by
  ext <;> simp [adapt, unadapt]
@[simp] theorem adapt_unadapt (p : Point k) : adapt (unadapt p) = p := by
  ext <;> simp [adapt, unadapt]

theorem equation_adapt (P : k[X]) (p : Point k) :
    equation P (adapt p) = originalEquation P p := by
  dsimp [equation, originalEquation, adapt]
  ring

/-- Words in the four actions conjugated by the explicitly invertible polynomial map adapt. -/
def OriginalReaches (P : k[X]) (n : ℕ) (p q : Point k) : Prop :=
  Reaches P n (adapt p) (adapt q)

theorem original_transitive_thirteen [IsAlgClosed k] (P : k[X]) (hP : P.natDegree ≠ 0)
    (p q : Point k) (hp : originalEquation P p = 0) (hq : originalEquation P q = 0) :
    OriginalReaches P 13 p q := by
  apply transitive_thirteen P hP (adapt p) (adapt q)
  · rwa [equation_adapt]
  · rwa [equation_adapt]

#print axioms original_transitive_thirteen
end ZariskiCylinder
