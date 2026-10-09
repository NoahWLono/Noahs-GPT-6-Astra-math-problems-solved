import Inputs.C003
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C003
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 3) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 3)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 64), (1, 256), (2, 128), (3, 512), (4, 2048), (5, 1024), (6, 1), (7, 4), (8, 2), (9, 8), (10, 32), (11, 16)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 3) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 3) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 3) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C003
