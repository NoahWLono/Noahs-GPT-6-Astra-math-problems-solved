import Inputs.C066
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C066
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 66) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 66)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3360), (1, 2992), (2, 3800), (3, 388), (4, 326), (5, 451), (6, 2100), (7, 3118), (8, 1595), (9, 262), (10, 389), (11, 199)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 66) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 66) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 66) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C066
