import Inputs.C119
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C119
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 119) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 119)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3544), (1, 2680), (2, 3952), (3, 3715), (4, 711), (5, 2822), (6, 23), (7, 25), (8, 37), (9, 62), (10, 13), (11, 47)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 119) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 119) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 119) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C119
