import Inputs.C188
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C188
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 188) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 188)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2392), (1, 3256), (2, 1648), (3, 2691), (4, 1223), (5, 774), (6, 21), (7, 26), (8, 33), (9, 44), (10, 22), (11, 11)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 188) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 188) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 188) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C188
