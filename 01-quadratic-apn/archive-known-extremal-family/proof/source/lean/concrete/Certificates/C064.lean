import Inputs.C064
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C064
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 64) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 64)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3584), (1, 512), (2, 2560), (3, 448), (4, 64), (5, 320), (6, 56), (7, 8), (8, 40), (9, 7), (10, 1), (11, 5)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 64) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 64) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 64) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C064
