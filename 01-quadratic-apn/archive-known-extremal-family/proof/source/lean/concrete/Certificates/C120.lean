import Inputs.C120
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C120
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 120) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 120)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2480), (1, 3432), (2, 2040), (3, 3526), (4, 2629), (5, 3911), (6, 62), (7, 13), (8, 47), (9, 52), (10, 46), (11, 59)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 120) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 120) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 120) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C120
