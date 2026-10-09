import Inputs.C195
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C195
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 195) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 195)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3200), (1, 2752), (2, 3840), (3, 1024), (4, 1536), (5, 2048), (6, 2), (7, 3), (8, 4), (9, 22), (10, 29), (11, 39)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 195) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 195) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 195) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C195
