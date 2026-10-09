import Inputs.C124
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C124
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 124) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 124)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2040), (1, 3656), (2, 3432), (3, 3783), (4, 961), (5, 2949), (6, 31), (7, 57), (8, 53), (9, 59), (10, 15), (11, 46)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 124) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 124) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 124) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C124
