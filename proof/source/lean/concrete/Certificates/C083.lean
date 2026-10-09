import Inputs.C083
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C083
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 83) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 83)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2624), (1, 1280), (2, 640), (3, 832), (4, 2176), (5, 1088), (6, 3625), (7, 532), (8, 2570), (9, 461), (10, 98), (11, 337)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 83) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 83) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 83) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C083
