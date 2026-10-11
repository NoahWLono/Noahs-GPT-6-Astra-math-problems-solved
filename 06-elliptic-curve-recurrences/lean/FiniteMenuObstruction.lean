import FiniteAgreementObstruction

/-! T3: the finite-menu union bound, using actual projective evaluations
and the established T2 coincidence theorem for each reduced rational map. -/
namespace Astra01.EllipticPointDivisor
noncomputable section
open WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
local instance : DecidableEq k := Classical.decEq _

/-- A reduced nonconstant rational map has a nonzero numerator. -/
theorem reduced_numerator_ne_zero (p q : k[X]) (hpq : IsCoprime p q)
    (hr : 1 ≤ max p.natDegree q.natDegree) : p ≠ 0 := by
  intro hp
  rw [hp] at hpq hr
  have hq := Polynomial.natDegree_eq_zero_of_isUnit (isCoprime_zero_left.mp hpq)
  simp [hq] at hr

theorem finite_recurrence_menu_bound {ι : Type*} [Fintype ι]
    (G : W.Point) (n : ℕ) (hn : 2 ≤ n) (horder : addOrderOf G = n)
    (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : ι → k[X]) (hq : ∀ j, q j ≠ 0) (hpq : ∀ j, IsCoprime (p j) (q j))
    (hr : ∀ j, 1 ≤ max (p j).natDegree (q j).natDegree)
    (S : Finset W.Point) (hS : ∀ P ∈ S, P ∈ AddSubgroup.zmultiples G)
    (hcover : ∀ P ∈ S, ∃ j, projectiveValue W K f (P + G) =
      projectiveValue W K (Polynomial.aeval f (p j) / Polynomial.aeval f (q j)) P) :
    S.card ≤ min n (divisorDegree W
      (poleDivisor W K (Units.mk0 f (by simpa using hf 0))) *
      ∑ j, (max (p j).natDegree (q j).natDegree + 1)) := by
  classical
  let D := divisorDegree W (poleDivisor W K (Units.mk0 f (by simpa using hf 0)))
  let A : ι → Finset W.Point := fun j => S.filter fun P => projectiveValue W K f (P + G) =
    projectiveValue W K (Polynomial.aeval f (p j) / Polynomial.aeval f (q j)) P
  have hA : ∀ j, (A j).card ≤ D * (max (p j).natDegree (q j).natDegree + 1) := by
    intro j
    have ht := finite_recurrence_agreement_bound W K G n hn horder f hf (p j) (q j)
      (reduced_numerator_ne_zero (p j) (q j) (hpq j) (hr j)) (hq j) (hpq j) (A j)
      (fun P hP => hS P (Finset.mem_filter.mp hP).1)
      (fun P hP => (Finset.mem_filter.mp hP).2)
    exact (le_min_iff.mp ht).2
  have hsub : S ⊆ Finset.univ.biUnion A := by
    intro P hP
    obtain ⟨j, hj⟩ := hcover P hP
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hP, hj⟩⟩
  apply le_min (finite_cyclic_subset_card_le W G n (by omega) horder S hS)
  change S.card ≤ D * ∑ j, (max (p j).natDegree (q j).natDegree + 1)
  calc
    S.card ≤ (Finset.univ.biUnion A).card := Finset.card_le_card hsub
    _ ≤ ∑ j, (A j).card := Finset.card_biUnion_le
    _ ≤ ∑ j, D * (max (p j).natDegree (q j).natDegree + 1) :=
      Finset.sum_le_sum fun j _ => hA j
    _ = D * ∑ j, (max (p j).natDegree (q j).natDegree + 1) := (Finset.mul_sum _ _ _).symm

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.finite_recurrence_menu_bound
