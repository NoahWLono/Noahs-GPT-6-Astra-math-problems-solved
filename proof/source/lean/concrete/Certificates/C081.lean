import Inputs.C081
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C081
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 81) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 81)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3056), (1, 1128), (2, 888), (3, 838), (4, 2181), (5, 1095), (6, 559), (7, 2065), (8, 1037), (9, 77), (10, 290), (11, 145)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 81) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 81) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 81) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C081
