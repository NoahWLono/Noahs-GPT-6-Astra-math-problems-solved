import Inputs.C007
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C007
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 7) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 7)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 64), (1, 256), (2, 128), (3, 576), (4, 2304), (5, 1152), (6, 9), (7, 36), (8, 18), (9, 8), (10, 32), (11, 16)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 7) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 7) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 7) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C007
