import Inputs.C063
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C063
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 63) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 63)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3752), (1, 720), (2, 2824), (3, 1477), (4, 1602), (5, 2369), (6, 58), (7, 11), (8, 44), (9, 23), (10, 25), (11, 37)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 63) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 63) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 63) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C063
