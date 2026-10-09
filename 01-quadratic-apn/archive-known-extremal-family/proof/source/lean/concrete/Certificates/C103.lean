import Inputs.C103
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C103
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 103) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 103)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3352), (1, 3000), (2, 3824), (3, 2179), (4, 3271), (5, 1798), (6, 1556), (7, 3614), (8, 3107), (9, 230), (10, 501), (11, 415)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 103) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 103) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 103) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C103
