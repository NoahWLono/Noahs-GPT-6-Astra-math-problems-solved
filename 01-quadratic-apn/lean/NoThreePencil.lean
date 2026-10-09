import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.CharP.Two

namespace NoThreePencil
abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
abbrev Bilin := V 4 →ₗ[F] V 4 →ₗ[F] F

def e (i : Fin 4) : V 4 := Pi.single i 1

def pf (B : Bilin) : F :=
  B (e 0) (e 1) * B (e 2) (e 3) +
  B (e 0) (e 2) * B (e 1) (e 3) +
  B (e 0) (e 3) * B (e 1) (e 2)

/-- Explicit four-dimensional alternating determinant equals the square of its
three-term Pfaffian in characteristic two. -/
theorem alternating_det (a b c d e f : F) :
    Matrix.det !![0,a,b,c; a,0,d,e; b,d,0,f; c,e,f,0] =
      (a*f+b*e+c*d)^2 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  ring_nf
  simp only [show (2:F)=0 by decide, mul_zero, add_zero, zero_add, CharTwo.sub_eq_add, add_assoc]

private theorem binary (a : F) : a = 0 ∨ a = 1 := by
  have h := ZMod.val_lt a
  have h' : a.val = 0 ∨ a.val = 1 := by omega
  rcases h' with h' | h'
  · left; exact ZMod.val_injective 2 (by simpa using h')
  · right; exact ZMod.val_injective 2 (by simpa using h')

/-- The three-term Pfaffian vanishes only for singular alternating 4-by-4 matrices.
The small finite algebra check supplies a nonzero radical vector, not an axiom. -/
theorem pf_zero_kernel : ∀ a b c d e f : F,
    a*f+b*e+c*d=0 → ∃ x : V 4, x ≠ 0 ∧
    a*x 1+b*x 2+c*x 3=0 ∧
    a*x 0+d*x 2+e*x 3=0 ∧
    b*x 0+d*x 1+f*x 3=0 ∧
    c*x 0+e*x 1+f*x 2=0 := by
  decide

theorem vector_expand (x : V 4) :
    x = x 0 • e 0 + x 1 • e 1 + x 2 • e 2 + x 3 • e 3 := by
  ext i
  fin_cases i <;> simp [e, Pi.single_apply]

theorem symmetric_of_alternating (B : Bilin) (h : ∀x, B x x=0) (x y : V 4) :
    B x y = B y x := by
  have hh := h (x+y)
  simp only [map_add, LinearMap.add_apply, h, zero_add, add_zero] at hh
  have htwo : B y x + B y x = 0 := CharTwo.add_self_eq_zero _
  linear_combination hh - htwo

theorem pf_ne_zero (B : Bilin) (h : ∀x, B x x=0)
    (hn : ∀x, (∀y, B x y=0) → x=0) : pf B ≠ 0 := by
  intro hp
  obtain ⟨x, hx, h0, h1, h2, h3⟩ := pf_zero_kernel
    (B (e 0) (e 1)) (B (e 0) (e 2)) (B (e 0) (e 3))
    (B (e 1) (e 2)) (B (e 1) (e 3)) (B (e 2) (e 3)) hp
  have hs := symmetric_of_alternating B h
  have hz : ∀ j, B x (e j)=0 := by
    intro j
    rw [vector_expand x]
    fin_cases j <;> simp only [Fin.reduceFinMk] <;>
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, h, hs (e 1) (e 0), hs (e 2) (e 0), hs (e 3) (e 0),
        hs (e 2) (e 1), hs (e 3) (e 1), hs (e 3) (e 2),
        mul_zero, zero_add, add_zero]
    · simpa only [mul_comm] using h0
    · simpa only [mul_comm] using h1
    · simpa only [mul_comm] using h2
    · simpa only [mul_comm] using h3
  apply hx
  apply hn x
  intro y
  rw [vector_expand y]
  simp [hz]

/-- Third additive differences of the quadratic Pfaffian vanish. -/
theorem pf_parity (A B C : Bilin) :
    pf A + pf B + pf C + pf (A+B) + pf (A+C) + pf (B+C) + pf (A+B+C)=0 := by
  simp only [pf, LinearMap.add_apply]
  ring_nf
  simp only [show (2:F)=0 by decide, show (4:F)=0 by decide, mul_zero, add_zero]

/-- No three-dimensional binary linear pencil of alternating forms on a
four-dimensional space is nondegenerate in every nonzero direction. -/
theorem no_three_pencil (L : V 3 →ₗ[F] Bilin)
    (ha : ∀u x, L u x x=0)
    (hn : ∀u, u≠0 → ∀x, (∀y, L u x y=0) → x=0) : False := by
  let a : V 3 := ![1,0,0]
  let b : V 3 := ![0,1,0]
  let c : V 3 := ![0,0,1]
  have hq (u : V 3) (hu : u≠0) : pf (L u)=1 := by
    rcases binary (pf (L u)) with hz | ho
    · exact False.elim (pf_ne_zero (L u) (ha u) (hn u hu) hz)
    · exact ho
  have habc : a≠0 ∧ b≠0 ∧ c≠0 ∧ a+b≠0 ∧ a+c≠0 ∧ b+c≠0 ∧ a+b+c≠0 := by
    decide
  obtain ⟨ha0,hb0,hc0,hab0,hac0,hbc0,habc0⟩ := habc
  have hp := pf_parity (L a) (L b) (L c)
  simp only [← map_add] at hp
  rw [hq a ha0, hq b hb0, hq c hc0, hq (a+b) hab0, hq (a+c) hac0,
    hq (b+c) hbc0, hq (a+b+c) habc0] at hp
  norm_num only at hp
  exact (by decide : (7:F)≠0) hp

#print axioms alternating_det
#print axioms pf_zero_kernel
#print axioms pf_parity
#print axioms no_three_pencil
end NoThreePencil
