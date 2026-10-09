import Inputs.C155
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C155
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 155) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 155)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2112), (1, 3328), (2, 1664), (3, 896), (4, 2368), (5, 1472), (6, 1585), (7, 3628), (8, 3130), (9, 204), (10, 486), (11, 403)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 155) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 155) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 155) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C155
