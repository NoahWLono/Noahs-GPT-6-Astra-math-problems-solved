import Inputs.C205
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C205
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 205) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 205)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2520), (1, 3192), (2, 1904), (3, 2243), (4, 3527), (5, 1926), (6, 1567), (7, 3641), (8, 3125), (9, 228), (10, 502), (11, 411)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 205) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 205) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 205) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C205
