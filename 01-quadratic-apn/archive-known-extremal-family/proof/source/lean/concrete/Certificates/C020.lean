import Inputs.C020
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C020
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 20) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 20)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 320), (1, 128), (2, 64), (3, 3008), (4, 1088), (5, 832), (6, 2621), (7, 1034), (8, 553), (9, 360), (10, 144), (11, 72)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 20) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 20) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 20) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C020
