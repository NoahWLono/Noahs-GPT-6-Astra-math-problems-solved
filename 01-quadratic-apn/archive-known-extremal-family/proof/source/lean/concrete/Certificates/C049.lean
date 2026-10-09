import Inputs.C049
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C049
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 49) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 49)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 304), (1, 424), (2, 248), (3, 3078), (4, 2565), (5, 3591), (6, 1028), (7, 1542), (8, 2051), (9, 176), (10, 232), (11, 312)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 49) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 49) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 49) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C049
