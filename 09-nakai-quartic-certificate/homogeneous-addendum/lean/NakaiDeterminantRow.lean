import NakaiJacobi
import Mathlib.RingTheory.Ideal.Operations

/-! Elementary adjugate row identities over arbitrary commutative rings. -/
noncomputable section
open scoped BigOperators
namespace NakaiDeterminantRow
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

def rowValue (M : Matrix ι ι R) (x : ι → R) (i : ι) : R := ∑ j, M i j * x j

lemma adjugate_rows (M : Matrix ι ι R) (x : ι → R) (q : ι) :
    (∑ l, M.adjugate q l * rowValue M x l) = M.det * x q := by
  calc
    _ = ∑ j, (∑ l, M.adjugate q l * M l j) * x j := by
      simp only [rowValue, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ j, (if q = j then M.det else 0) * x j := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      have hh := congrArg (fun N : Matrix ι ι R => N q j) (Matrix.adjugate_mul M)
      simpa [Matrix.mul_apply, Matrix.one_apply] using hh
    _ = _ := by simp [ite_mul]

lemma det_updateRow_eq_sum (M : Matrix ι ι R) (r : ι) (u : ι → R) :
    (M.updateRow r u).det = ∑ j, M.adjugate j r * u j := by
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  rfl

/-- A basic variable-syzygy row has determinant in the ideal of row outputs.
The basis-row adjugate calculation is valid over any commutative ring. -/
theorem cofactor_wedge_mem (M : Matrix ι ι R) (x : ι → R) (I : Ideal R)
    (hy : ∀ l, rowValue M x l ∈ I) (r p q : ι) :
    x q * M.adjugate p r - x p * M.adjugate q r ∈ I := by
  let L : Matrix ι ι R := M.updateRow r (Pi.single p 1)
  have hLrow : rowValue L x r = x p := by
    simp [rowValue, L, Pi.single_apply, ite_mul]
  have hLdet : L.det = M.adjugate p r := (Matrix.adjugate_apply M p r).symm
  have hLadj : L.adjugate q r = M.adjugate q r := by
    simp only [L, Matrix.adjugate_apply, Matrix.updateRow_idem]
  have he := Finset.sum_erase_add Finset.univ
    (fun l => L.adjugate q l * rowValue L x l) (Finset.mem_univ r)
  rw [hLrow, adjugate_rows, hLdet, hLadj] at he
  have hw : x q * M.adjugate p r - x p * M.adjugate q r =
      ∑ l ∈ Finset.univ.erase r, L.adjugate q l * rowValue L x l := by
    calc
      _ = M.adjugate p r * x q - M.adjugate q r * x p := by ring
      _ = _ := (eq_sub_of_add_eq he).symm
  rw [hw]
  apply Submodule.sum_mem
  intro l hl
  apply Ideal.mul_mem_left
  have hlr : l ≠ r := (Finset.mem_erase.mp hl).1
  simpa only [rowValue, L, Matrix.updateRow_ne hlr] using hy l

#print axioms cofactor_wedge_mem
end NakaiDeterminantRow
