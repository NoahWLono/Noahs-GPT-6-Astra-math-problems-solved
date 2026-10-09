import Inputs.C242
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C242
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 242) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 242)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3192), (1, 2824), (2, 3752), (3, 2567), (4, 1025), (5, 517), (6, 2049), (7, 3076), (8, 1538), (9, 302), (10, 405), (11, 207)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 242) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 242) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 242) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C242
