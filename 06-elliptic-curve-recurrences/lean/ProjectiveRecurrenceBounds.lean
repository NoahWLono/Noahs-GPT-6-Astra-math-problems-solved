import RationalProjectiveComposition

/-! T2 and T3 with the actual outer rational projective map, and with the
complete agreement subsets of the finite cyclic subgroup. The degree of f
is its actual pole-divisor degree; the reduced map p/q has degree max(deg p,deg q). -/
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

/-- Canonical finite enumeration of the cyclic subgroup when G has finite order. -/
def cyclicPoints (G : W.Point) : Finset W.Point := by
  classical
  exact Finset.univ.image (fun i : Fin (addOrderOf G) => i.val • G)

theorem mem_cyclicPoints_iff (G P : W.Point) (hG : 0 < addOrderOf G) :
    P ∈ cyclicPoints W G ↔ P ∈ AddSubgroup.zmultiples G := by
  classical
  constructor
  · intro hP
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hP
    exact hi ▸ AddSubgroup.nsmul_mem_zmultiples G i.val
  · intro hP
    obtain ⟨i, hi⟩ := (finEquivZMultiples (addOrderOf_pos_iff.mp hG)).surjective ⟨P, hP⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩

/-- T2, as a bound on any finite set of projective recurrence agreements. -/
theorem rational_recurrence_agreement_bound (G : W.Point) (n : ℕ) (hn : 2 ≤ n)
    (horder : addOrderOf G = n) (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : k[X]) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (hr : 1 ≤ max p.natDegree q.natDegree)
    (S : Finset W.Point) (hS : ∀ P ∈ S, P ∈ AddSubgroup.zmultiples G)
    (hagree : ∀ P ∈ S, projectiveValue W K f (P + G) =
      rationalProjectiveMap p q (projectiveValue W K f P)) :
    S.card ≤ min n (divisorDegree W
      (poleDivisor W K (Units.mk0 f (by simpa using hf 0))) *
      (max p.natDegree q.natDegree + 1)) := by
  have hp := reduced_numerator_ne_zero p q hpq hr
  apply finite_recurrence_agreement_bound W K G n hn horder f hf p q hp hq hpq S hS
  intro P hP
  rw [projectiveValue_rational_composition W K f hf p q hp hq hpq P]
  exact hagree P hP

/-- T2 for the entire projective agreement set in H=⟨G⟩, including all poles. -/
theorem full_agreement_set_bound (G : W.Point) (n : ℕ) (hn : 2 ≤ n)
    (horder : addOrderOf G = n) (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : k[X]) (hq : q ≠ 0) (hpq : IsCoprime p q)
    (hr : 1 ≤ max p.natDegree q.natDegree) :
    ((cyclicPoints W G).filter fun P => projectiveValue W K f (P + G) =
      rationalProjectiveMap p q (projectiveValue W K f P)).card ≤
      min n (divisorDegree W (poleDivisor W K (Units.mk0 f (by simpa using hf 0))) *
        (max p.natDegree q.natDegree + 1)) := by
  classical
  apply rational_recurrence_agreement_bound W K G n hn horder f hf p q hq hpq hr
  · intro P hP
    exact (mem_cyclicPoints_iff W G P (by omega)).mp (Finset.mem_filter.mp hP).1
  · intro P hP
    exact (Finset.mem_filter.mp hP).2

/-- T3 for the complete agreement set of a fixed finite family of rational maps. -/
theorem full_menu_agreement_set_bound {ι : Type*} [Fintype ι]
    (G : W.Point) (n : ℕ) (hn : 2 ≤ n) (horder : addOrderOf G = n)
    (f : K) (hf : ∀ c : k, f ≠ algebraMap k K c)
    (p q : ι → k[X]) (hq : ∀ j, q j ≠ 0) (hpq : ∀ j, IsCoprime (p j) (q j))
    (hr : ∀ j, 1 ≤ max (p j).natDegree (q j).natDegree) :
    ((cyclicPoints W G).filter fun P => ∃ j, projectiveValue W K f (P + G) =
      rationalProjectiveMap (p j) (q j) (projectiveValue W K f P)).card ≤
      min n (divisorDegree W (poleDivisor W K (Units.mk0 f (by simpa using hf 0))) *
        ∑ j, (max (p j).natDegree (q j).natDegree + 1)) := by
  classical
  apply finite_recurrence_menu_bound W K G n hn horder f hf p q hq hpq hr
  · intro P hP
    exact (mem_cyclicPoints_iff W G P (by omega)).mp (Finset.mem_filter.mp hP).1
  · intro P hP
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hP).2
    refine ⟨j, ?_⟩
    rw [projectiveValue_rational_composition W K f hf (p j) (q j)
      (reduced_numerator_ne_zero (p j) (q j) (hpq j) (hr j)) (hq j) (hpq j) P]
    exact hj

end
end Astra01.EllipticPointDivisor
#print axioms Astra01.EllipticPointDivisor.full_agreement_set_bound
#print axioms Astra01.EllipticPointDivisor.full_menu_agreement_set_bound
