import Inputs.C168
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C168
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 168) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 168)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2032), (1, 3688), (2, 3448), (3, 4038), (4, 581), (5, 2887), (6, 3135), (7, 2569), (8, 3629), (9, 443), (10, 335), (11, 494)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 168) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 168) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 168) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C168
