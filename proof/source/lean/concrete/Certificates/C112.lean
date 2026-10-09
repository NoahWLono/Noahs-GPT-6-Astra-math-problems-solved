import Inputs.C112
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C112
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 112) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 112)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1096), (1, 1824), (2, 2192), (3, 641), (4, 2244), (5, 1282), (6, 17), (7, 28), (8, 34), (9, 10), (10, 35), (11, 20)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 112) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 112) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 112) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C112
