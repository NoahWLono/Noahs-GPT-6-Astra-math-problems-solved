import Inputs.C065
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C065
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 65) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 65)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3104), (1, 2608), (2, 3608), (3, 2436), (4, 3398), (5, 1987), (6, 2096), (7, 3112), (8, 1592), (9, 294), (10, 437), (11, 223)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 65) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 65) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 65) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C065
