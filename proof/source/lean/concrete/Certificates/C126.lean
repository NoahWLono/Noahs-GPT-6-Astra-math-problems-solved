import Inputs.C126
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C126
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 126) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 126)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3872), (1, 944), (2, 2776), (3, 964), (4, 2118), (5, 1347), (6, 2620), (7, 1038), (8, 555), (9, 335), (10, 161), (11, 85)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 126) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 126) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 126) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C126
