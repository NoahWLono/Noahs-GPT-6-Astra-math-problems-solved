import Inputs.C136
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C136
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 136) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 136)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2688), (1, 1216), (2, 768), (3, 1152), (4, 1728), (5, 2304), (6, 18), (7, 27), (8, 36), (9, 21), (10, 26), (11, 33)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 136) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 136) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 136) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C136
