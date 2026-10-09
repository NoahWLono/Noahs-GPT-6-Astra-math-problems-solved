import Inputs.C203
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C203
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 203) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 203)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1152), (1, 1728), (2, 2304), (3, 1024), (4, 1536), (5, 2048), (6, 2), (7, 3), (8, 4), (9, 18), (10, 27), (11, 36)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 203) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 203) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 203) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C203
