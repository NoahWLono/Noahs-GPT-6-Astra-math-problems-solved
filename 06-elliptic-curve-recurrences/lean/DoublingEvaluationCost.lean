import EllipticDoublingIteration

/-! A precise group-operation model: the recursive evaluator performs one
point doubling per step, then reads x once. No field/bit-operation or runtime
lower bound is inferred from the degree. -/
namespace Astra01.EllipticDuplication
noncomputable section

section Trace
variable {A : Type*} [AddCommMonoid A]
/-- The second component counts charged point doublings; the initial point is input. -/
def doublingTrace (P : A) : ℕ → A × ℕ
  | 0 => (P,0)
  | t+1 => let previous := doublingTrace P t
           (previous.1+previous.1,previous.2+1)

theorem doublingTrace_correct (P : A) (t : ℕ) :
    doublingTrace P t = ((2^t) • P,t) := by
  induction t with
  | zero => simp [doublingTrace]
  | succ t ih => simp [doublingTrace, ih, pow_succ', mul_nsmul, two_nsmul, nsmul_add]
end Trace

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Chart FunctionField FunctionField.Chart
open Astra01.EllipticPointDivisor
open scoped RatFunc Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance : DecidableEq k := Classical.decEq _

/-- E4: degree 2·4^t, and a correct evaluator charged exactly t doublings. -/
theorem exponential_degree_linear_doublings (h2 : (2:k) ≠ 0) (t : ℕ) (P : W.Point) :
    divisorDegree W (poleDivisor W K (iteratedUnit W K h2 t)) = 2*4^t ∧
    (coordinateXValue W (doublingTrace P t).1, (doublingTrace P t).2) =
      (projectiveValue W K (iteratedFunction W K t) P,t) := by
  refine ⟨iterated_degree W K h2 t, ?_⟩
  rw [doublingTrace_correct, iterated_projective_value W K h2]

theorem degree_at_eight (h2 : (2:k) ≠ 0) :
    divisorDegree W (poleDivisor W K (iteratedUnit W K h2 8)) = 131072 := by
  rw [iterated_degree W K h2]
  norm_num
end
end Astra01.EllipticDuplication
#print axioms Astra01.EllipticDuplication.exponential_degree_linear_doublings
#print axioms Astra01.EllipticDuplication.degree_at_eight
