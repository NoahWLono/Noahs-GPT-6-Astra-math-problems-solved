import Inputs.C093
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C093
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 93) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 93)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3688), (1, 784), (2, 2696), (3, 2501), (4, 3138), (5, 1857), (6, 2105), (7, 3084), (8, 1578), (9, 295), (10, 433), (11, 221)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 93) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 93) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 93) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C093
