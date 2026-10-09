import Inputs.C235
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C235
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 235) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 235)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1784), (1, 4040), (2, 3496), (3, 1543), (4, 3585), (5, 3077), (6, 3587), (7, 519), (8, 2566), (9, 475), (10, 127), (11, 374)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 235) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 235) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 235) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C235
