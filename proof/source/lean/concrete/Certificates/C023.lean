import Inputs.C023
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C023
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 23) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 23)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 384), (1, 320), (2, 448), (3, 3200), (4, 2752), (5, 3840), (6, 2070), (7, 3101), (8, 1575), (9, 304), (10, 424), (11, 248)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 23) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 23) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 23) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C023
