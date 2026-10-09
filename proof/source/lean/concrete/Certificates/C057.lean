import Inputs.C057
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C057
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 57) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 57)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1328), (1, 1960), (2, 2296), (3, 3078), (4, 2565), (5, 3591), (6, 1028), (7, 1542), (8, 2051), (9, 178), (10, 235), (11, 316)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 57) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 57) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 57) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C057
