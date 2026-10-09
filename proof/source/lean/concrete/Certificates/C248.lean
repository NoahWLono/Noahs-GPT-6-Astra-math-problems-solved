import Inputs.C248
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C248
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 248) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 248)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3784), (1, 992), (2, 2960), (3, 1537), (4, 3588), (5, 3074), (6, 3), (7, 7), (8, 6), (9, 31), (10, 57), (11, 53)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 248) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 248) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 248) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C248
