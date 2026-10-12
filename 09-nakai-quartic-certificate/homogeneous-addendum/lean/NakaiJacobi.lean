import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

/-!
A generic algebraic Jacobi identity for a ring derivation. This private module
is infrastructure only; it does not assert Hessian nonmembership or a generic
Nakai theorem. No field, matrix invertibility, or characteristic assumption is
needed for the determinant identity.
-/

noncomputable section
open scoped BigOperators

namespace NakaiJacobi
variable {k R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]

lemma derivation_prod (D : Derivation k R R) [DecidableEq ι]
    (s : Finset ι) (f : ι → R) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha]
      simp only [Finset.erase_insert ha, smul_eq_mul]
      rw [Finset.mul_sum]
      have hsum : (∑ i ∈ s, f a * (D (f i) * ∏ j ∈ s.erase i, f j)) =
          ∑ i ∈ s, D (f i) * ∏ j ∈ (insert a s).erase i, f j := by
        apply Finset.sum_congr rfl
        intro i hi
        have hia : i ≠ a := by
          intro h
          exact ha (h ▸ hi)
        rw [Finset.erase_insert_of_ne hia.symm, Finset.prod_insert]
        · ring
        · exact fun h => ha (Finset.mem_of_mem_erase h)
      rw [hsum]
      ring

lemma prod_updateCol [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (j : ι) (v : ι → R) (σ : Equiv.Perm ι) :
    (∏ i, (A.updateCol j v) (σ i) i) =
      v (σ j) * ∏ i ∈ Finset.univ.erase j, A (σ i) i := by
  calc
    (∏ i, (A.updateCol j v) (σ i) i) =
        ∏ i, Function.update (fun i => A (σ i) i) j (v (σ j)) i := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i = j
      · subst i
        simp
      · simp [h]
    _ = _ := by
      simpa only [Finset.sdiff_singleton_eq_erase] using
        (Finset.prod_update_of_mem (Finset.mem_univ j)
          (fun i => A (σ i) i) (v (σ j)))

/-- Differentiate the determinant by differentiating one column at a time. -/
theorem derivation_det_columns [Fintype ι] [DecidableEq ι]
    (D : Derivation k R R) (A : Matrix ι ι R) :
    D A.det = ∑ j, (A.updateCol j (fun i => D (A i j))).det := by
  rw [Matrix.det_apply']
  simp only [map_sum, D.leibniz, Derivation.map_intCast, smul_eq_mul, mul_zero,
    add_zero, derivation_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  rw [prod_updateCol]

/-- Jacobi's formula for an arbitrary algebra derivation over a commutative ring. -/
theorem derivation_det [Fintype ι] [DecidableEq ι]
    (D : Derivation k R R) (A : Matrix ι ι R) :
    D A.det = ∑ i, ∑ j, A.adjugate j i * D (A i j) := by
  rw [derivation_det_columns, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

#print axioms derivation_prod
#print axioms derivation_det_columns
#print axioms derivation_det
end NakaiJacobi
