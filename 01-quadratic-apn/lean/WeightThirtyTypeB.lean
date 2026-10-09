import WeightThirtyModel
import Mathlib.Tactic.Ring

namespace BooleanANF

/-- Coordinate splitting that does not require a new ambient vector-space type. -/
def firstThreeZero (x : Block) : Prop := ∀ i : Fin 4, i ≠ 3 → x i = 0
instance (x : Block) : Decidable (firstThreeZero x) := inferInstanceAs (Decidable (∀ i : Fin 4, i ≠ 3 → x i = 0))

def typeBResidual (z : DoubleBlock) : F₂ :=
  let x : Block := fun i => z (.inl i)
  let y : Block := fun i => z (.inr i)
  if y 3 = 0 ∧ ¬firstThreeZero y ∧
    (firstThreeZero x ∨ ∀ i : Fin 4, i ≠ 3 → x i = y i) then 1 else 0

def typeBLinear (z : DoubleBlock) : DoubleBlock := Sum.elim
  (fun i => if i = 3 then z (.inl 3) + z (.inr 3) else z (.inr i))
  (fun i => if i = 3 then z (.inl 3) else z (.inl i) + z (.inr i))

def typeBInverse (z : DoubleBlock) : DoubleBlock := Sum.elim
  (fun i => if i = 3 then z (.inr 3) else z (.inr i) + z (.inl i))
  (fun i => if i = 3 then z (.inl 3) + z (.inr 3) else z (.inl i))

/-- The columns are the directions of the two reconstructed four-flats. -/
def typeBEquiv : DoubleBlock ≃ₗ[F₂] DoubleBlock where
  toFun := typeBLinear
  invFun := typeBInverse
  left_inv := by
    intro z
    funext i
    rcases i with i | i <;> by_cases h : i = 3 <;>
      simp only [typeBLinear, typeBInverse, Sum.elim_inl, Sum.elim_inr, h, if_true, if_false]
    all_goals ring_nf <;> simp [CharTwo.two_eq_zero]
  right_inv := by
    intro z
    funext i
    rcases i with i | i <;> by_cases h : i = 3 <;>
      simp only [typeBLinear, typeBInverse, Sum.elim_inl, Sum.elim_inr, h, if_true, if_false]
    all_goals ring_nf <;> simp [CharTwo.two_eq_zero]
  map_add' := by
    intro x y
    funext i
    rcases i with i | i <;> by_cases h : i = 3 <;>
      simp [typeBLinear, h, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro c x
    funext i
    rcases i with i | i <;> by_cases h : i = 3 <;>
      simp [typeBLinear, h, smul_add, mul_add]

def typeBPoint : DoubleBlock := Sum.elim
  (fun i => if i = 3 then 1 else 0) (fun _ => 0)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem typeB_identity_bits (a b c d e f g h : F₂) :
    residualSignal typeBResidual
      (typeBPoint + typeBEquiv (Sum.elim ![a,b,c,d] ![e,f,g,h])) =
      delta 0 ![a,b,c,d] + delta 0 ![e,f,g,h] := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases e <;> fin_cases f <;> fin_cases g <;> fin_cases h <;> decide

/-- Explicit semantic reconstruction; the linear equivalence certifies both
four-dimensionality and transversality, rather than only a truth-table match. -/
theorem typeB_twoTransverseFlats : TwoTransverseFlats (residualSignal typeBResidual) := by
  refine ⟨typeBPoint, typeBEquiv, ?_⟩
  intro x y
  have hx : x = ![x 0,x 1,x 2,x 3] := by funext i; fin_cases i <;> rfl
  have hy : y = ![y 0,y 1,y 2,y 3] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hx, hy]
  conv_rhs => rw [hx, hy]
  exact typeB_identity_bits _ _ _ _ _ _ _ _

end BooleanANF
