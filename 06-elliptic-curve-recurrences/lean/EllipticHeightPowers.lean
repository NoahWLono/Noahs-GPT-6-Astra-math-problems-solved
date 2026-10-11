import EllipticHeightNormalization

/-! Exact height scaling under coordinate powers, using actual normalized valuations. -/
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

local instance : Algebra k K := FunctionField.algebraConstants k K
local instance : IsScalarTower k k[X] K := FunctionField.algebraConstants_isScalarTower k K
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq K := Classical.decEq _

theorem vector_pow_ne_zero (z : ι → K) (hz : z ≠ 0) (n : ℕ) :
    (fun i => z i ^ n) ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  intro h
  exact pow_ne_zero n hi (congrFun h i)

theorem vectorDivisor_pow (z : ι → K) (hz : z ≠ 0) (n : ℕ) :
    vectorDivisor W K (fun i => z i ^ n) (vector_pow_ne_zero K z hz n) =
      n • vectorDivisor W K z hz := by
  ext P
  change vectorDivisor W K _ _ P = n • vectorDivisor W K z hz P
  obtain ⟨hb,⟨i,_,hi⟩⟩ := vectorDivisor_valuation W K z hz P
  apply vectorDivisor_eq_of_bounds
  · intro j
    rw [map_pow, WithZero.exp_nsmul]
    exact pow_le_pow_left' (hb j) n
  · refine ⟨i, ?_⟩
    rw [map_pow, hi, WithZero.exp_nsmul]

theorem vectorHeight_pow (z : ι → K) (hz : z ≠ 0) (n : ℕ) :
    vectorHeight W K (fun i => z i ^ n) (vector_pow_ne_zero K z hz n) =
      n • vectorHeight W K z hz := by
  unfold vectorHeight
  rw [vectorDivisor_pow]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ih,
      succ_nsmul]

end
end Astra01.EllipticHeight
#print axioms Astra01.EllipticHeight.vectorDivisor_pow
#print axioms Astra01.EllipticHeight.vectorHeight_pow
