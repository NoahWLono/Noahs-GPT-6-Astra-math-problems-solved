import Inputs.C062
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C062
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 62) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 62)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3728), (1, 728), (2, 2848), (3, 3010), (4, 1091), (5, 836), (6, 3642), (7, 523), (8, 2604), (9, 495), (10, 81), (11, 333)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 62) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 62) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 62) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C062
