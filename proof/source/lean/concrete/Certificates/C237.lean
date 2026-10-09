import Inputs.C237
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C237
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 237) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 237)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3744), (1, 752), (2, 2840), (3, 3908), (4, 646), (5, 2627), (6, 2090), (7, 3091), (8, 1548), (9, 319), (10, 393), (11, 237)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 237) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 237) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 237) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C237
