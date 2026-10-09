import Inputs.C139
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C139
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 139) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 139)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3264), (1, 3008), (2, 3968), (3, 1856), (4, 3712), (5, 3136), (6, 43), (7, 23), (8, 14), (9, 30), (10, 61), (11, 55)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 139) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 139) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 139) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C139
