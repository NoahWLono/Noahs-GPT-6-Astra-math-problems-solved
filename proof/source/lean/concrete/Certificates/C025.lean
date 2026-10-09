import Inputs.C025
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C025
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 25) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 25)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1296), (1, 1944), (2, 2272), (3, 3074), (4, 2563), (5, 3588), (6, 3076), (7, 2566), (8, 3587), (9, 434), (10, 363), (11, 508)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 25) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 25) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 25) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C025
