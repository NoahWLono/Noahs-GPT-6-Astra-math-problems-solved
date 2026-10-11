import EllipticCoincidenceDivisor
import Mathlib.Data.Finsupp.Order

/-! A genuine local projective-height divisor: at every point take the largest
negative order among the nonzero homogeneous coordinates. No morphism-degree
or height parallelogram axiom is assumed. -/
namespace Astra01.EllipticHeight
noncomputable section
open WeierstrassCurve.Affine.Chart FunctionField.Chart
open Astra01.EllipticPointDivisor
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq K := Classical.decEq _

def coordinateUnit (z : ι → K) (i : {i // z i ≠ 0}) : Kˣ := Units.mk0 (z i) i.2

theorem coordinate_nonempty (z : ι → K) (hz : z ≠ 0) : Nonempty {i // z i ≠ 0} := by
  classical
  by_contra h
  apply hz
  ext i
  by_contra hi
  exact h ⟨⟨i,hi⟩⟩

def vectorDivisor (z : ι → K) (hz : z ≠ 0) : W.Point →₀ ℤ := by
  classical
  letI := coordinate_nonempty K z hz
  exact Finset.univ.sup' Finset.univ_nonempty fun i : {i // z i ≠ 0} =>
    -principalDivisor W K (Additive.ofMul (coordinateUnit K z i))

theorem vectorDivisor_apply (z : ι → K) (hz : z ≠ 0) (P : W.Point) :
    vectorDivisor W K z hz P =
      letI := coordinate_nonempty K z hz
      Finset.univ.sup' Finset.univ_nonempty (fun i : {i // z i ≠ 0} =>
        -principalDivisor W K (Additive.ofMul (coordinateUnit K z i)) P) := by
  classical
  letI := coordinate_nonempty K z hz
  unfold vectorDivisor
  exact Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty (fun d : W.Point →₀ ℤ => d P)
    (fun _ _ => Finsupp.sup_apply _ _ P)

/-- The exponential of the height-divisor coefficient is exactly the largest
valuation of the actual homogeneous coordinates. -/
theorem vectorDivisor_valuation (z : ι → K) (hz : z ≠ 0) (P : W.Point) :
    (∀ i, placeValuation k K (placeOfPoint W K P) (z i) ≤
      WithZero.exp (vectorDivisor W K z hz P)) ∧
    ∃ i, z i ≠ 0 ∧ placeValuation k K (placeOfPoint W K P) (z i) =
      WithZero.exp (vectorDivisor W K z hz P) := by
  classical
  letI := coordinate_nonempty K z hz
  rw [vectorDivisor_apply]
  constructor
  · intro i
    by_cases hi : z i = 0
    · simp [hi]
    · have hb := Finset.le_sup' (fun j : {i // z i ≠ 0} =>
          -principalDivisor W K (Additive.ofMul (coordinateUnit K z j)) P)
          (Finset.mem_univ (⟨i,hi⟩ : {i // z i ≠ 0}))
      have hv := point_valuation_unit W K (coordinateUnit K z ⟨i,hi⟩) P
      change placeValuation k K (placeOfPoint W K P) (z i) = _ at hv
      rw [hv]
      exact WithZero.exp_le_exp.mpr hb
  · obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset {i // z i ≠ 0}))
      Finset.univ_nonempty (fun j => -principalDivisor W K (Additive.ofMul (coordinateUnit K z j)) P)
    refine ⟨i,i.2,?_⟩
    rw [hi]
    exact point_valuation_unit W K (coordinateUnit K z i) P
end
end Astra01.EllipticHeight
#print axioms Astra01.EllipticHeight.vectorDivisor_valuation
