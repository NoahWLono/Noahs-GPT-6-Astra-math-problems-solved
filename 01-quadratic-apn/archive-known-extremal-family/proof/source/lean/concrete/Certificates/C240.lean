import Inputs.C240
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C240
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 240) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 240)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1224), (1, 2016), (2, 2448), (3, 1537), (4, 3588), (5, 3074), (6, 3), (7, 7), (8, 6), (9, 26), (10, 59), (11, 52)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 240) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 240) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 240) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C240
