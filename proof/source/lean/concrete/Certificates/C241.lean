import Inputs.C241
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C241
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 241) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 241)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3448), (1, 2696), (2, 3688), (3, 519), (4, 2049), (5, 1029), (6, 2053), (7, 3074), (8, 1537), (9, 270), (10, 421), (11, 215)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 241) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 241) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 241) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C241
