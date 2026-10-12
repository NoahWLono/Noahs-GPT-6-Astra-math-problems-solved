import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
An explicit rational, four-variable, non-separated quartic certificate.
All computations below are checked by Lean's kernel; no external polynomial oracle
or native decision procedure is used.
-/
noncomputable section
namespace NakaiQuartic
open MvPolynomial
open scoped BigOperators

abbrev P := MvPolynomial (Fin 4) ℚ

def x (i : Fin 4) : P := X i

def F : P :=
  x 0 ^ 4 + x 1 ^ 4 + x 2 ^ 4 + x 3 ^ 4 +
  x 0 ^ 2 * x 1 ^ 2 + x 0 ^ 2 * x 2 ^ 2 + x 0 ^ 2 * x 3 ^ 2 +
  x 1 ^ 2 * x 2 ^ 2 + x 1 ^ 2 * x 3 ^ 2 + x 2 ^ 2 * x 3 ^ 2

def S : P := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2

def G (i : Fin 4) : P := pderiv i F

def H : Matrix (Fin 4) (Fin 4) P := fun i j => pderiv i (pderiv j F)
def C : Matrix (Fin 4) (Fin 4) P := H.adjugate
def h : P := H.det
def a (i : Fin 4) : P := C i 0
def B (i j : Fin 4) : P := a i * x j + x i * a j - x 0 * C i j

def mulMap (p : P) : Module.End ℚ P where
  toFun q := p * q
  map_add' q r := mul_add p q r
  map_smul' c q := by simp [Algebra.smul_def, mul_left_comm]

def QP : Module.End ℚ P :=
  (∑ i : Fin 4, ∑ j : Fin 4,
    (mulMap (B i j)).comp ((pderiv i).toLinearMap.comp (pderiv j).toLinearMap)) +
  6 • (∑ i : Fin 4, (mulMap (a i)).comp (pderiv i).toLinearMap)

@[simp] theorem QP_apply (p : P) :
    QP p = (∑ i : Fin 4, ∑ j : Fin 4, B i j * pderiv i (pderiv j p)) +
      6 * (∑ i : Fin 4, a i * pderiv i p) := by
  simp [QP, mulMap, Finset.sum_apply, nsmul_eq_mul, Finset.mul_sum]

def J : Ideal P := Ideal.span (Set.range G)

@[simp] theorem pderiv_x (i j : Fin 4) : pderiv i (x j) = if j = i then 1 else 0 := by
  simp [x, pderiv_X, Pi.single_apply]

@[simp] theorem pderiv_ofNat (i : Fin 4) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : P) = 0 := (pderiv i).map_natCast n

theorem G_formula (i : Fin 4) : G i = 2 * x i * (S + x i ^ 2) := by
  fin_cases i <;> simp [G, F, S] <;> ring


#print axioms NakaiQuartic.G_formula

def H₀ : Matrix (Fin 4) (Fin 4) P := fun i j =>
  if i = j then 2 * S + 10 * x i ^ 2 else 4 * x i * x j

theorem H_formula : H = H₀ := by
  funext i j
  change pderiv i (G j) = H₀ i j
  rw [G_formula]
  fin_cases i <;> fin_cases j <;>
    simp [H₀, S] <;> ring


#print axioms NakaiQuartic.H_formula

/-- A cofactor formula retaining the actual adjugate as the definition of C. -/
theorem C_formula (i j : Fin 4) : C i j =
    (-1) ^ (j.val + i.val) *
      (H₀ (j.succAbove 0) (i.succAbove 0) * H₀ (j.succAbove 1) (i.succAbove 1) * H₀ (j.succAbove 2) (i.succAbove 2)
      - H₀ (j.succAbove 0) (i.succAbove 0) * H₀ (j.succAbove 1) (i.succAbove 2) * H₀ (j.succAbove 2) (i.succAbove 1)
      - H₀ (j.succAbove 0) (i.succAbove 1) * H₀ (j.succAbove 1) (i.succAbove 0) * H₀ (j.succAbove 2) (i.succAbove 2)
      + H₀ (j.succAbove 0) (i.succAbove 1) * H₀ (j.succAbove 1) (i.succAbove 2) * H₀ (j.succAbove 2) (i.succAbove 0)
      + H₀ (j.succAbove 0) (i.succAbove 2) * H₀ (j.succAbove 1) (i.succAbove 0) * H₀ (j.succAbove 2) (i.succAbove 1)
      - H₀ (j.succAbove 0) (i.succAbove 2) * H₀ (j.succAbove 1) (i.succAbove 1) * H₀ (j.succAbove 2) (i.succAbove 0)) := by
  simp only [C, Matrix.adjugate_fin_succ_eq_det_submatrix, H_formula,
    Matrix.det_fin_three, Matrix.submatrix_apply]

/-- Concrete exponent tuples, used only to specify ordinary coefficients. -/
def exp4 (a b c d : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a,b,c,d]

@[simp] theorem exp4_apply0 (a b c d : ℕ) : exp4 a b c d 0 = a := rfl
@[simp] theorem exp4_apply1 (a b c d : ℕ) : exp4 a b c d 1 = b := rfl
@[simp] theorem exp4_apply2 (a b c d : ℕ) : exp4 a b c d 2 = c := rfl
@[simp] theorem exp4_apply3 (a b c d : ℕ) : exp4 a b c d 3 = d := rfl

theorem exp4_sub (a b c d w x y z : ℕ) :
    exp4 a b c d - exp4 w x y z = exp4 (a-w) (b-x) (c-y) (d-z) := by
  ext i; fin_cases i <;> rfl

theorem exp4_le (a b c d w x y z : ℕ) :
    exp4 a b c d ≤ exp4 w x y z ↔ a ≤ w ∧ b ≤ x ∧ c ≤ y ∧ d ≤ z := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨ha,hb,hc,hd⟩ i
    fin_cases i <;> assumption

theorem exp4_eq (a b c d w x y z : ℕ) :
    exp4 a b c d = exp4 w x y z ↔ a = w ∧ b = x ∧ c = y ∧ d = z := by
  constructor
  · intro h
    exact ⟨congrArg (fun e => e 0) h, congrArg (fun e => e 1) h,
      congrArg (fun e => e 2) h, congrArg (fun e => e 3) h⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩; rfl

theorem monomial_exp4 (a b c d : ℕ) :
    monomial (exp4 a b c d) (1 : ℚ) = x 0 ^ a * x 1 ^ b * x 2 ^ c * x 3 ^ d := by
  have he : exp4 a b c d = Finsupp.single 0 a + Finsupp.single 1 b +
      Finsupp.single 2 c + Finsupp.single 3 d := by
    ext i; fin_cases i <;> simp
  rw [he]
  simp only [monomial_add_single, ← X_pow_eq_monomial, x]

#print axioms NakaiQuartic.G_formula
#print axioms NakaiQuartic.H_formula
#print axioms NakaiQuartic.C_formula
end NakaiQuartic
