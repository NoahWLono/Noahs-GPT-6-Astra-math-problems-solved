import Inputs.C249
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C249
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 249) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 249)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1400), (1, 1672), (2, 2152), (3, 519), (4, 2049), (5, 1029), (6, 2053), (7, 3074), (8, 1537), (9, 266), (10, 419), (11, 212)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 249) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 249) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 249) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C249
