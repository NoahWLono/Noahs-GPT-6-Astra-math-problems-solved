import Inputs.C204
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C204
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 204) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 204)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1856), (1, 3712), (2, 3136), (3, 2944), (4, 1344), (5, 960), (6, 53), (7, 42), (8, 57), (9, 43), (10, 23), (11, 14)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 204) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 204) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 204) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C204
