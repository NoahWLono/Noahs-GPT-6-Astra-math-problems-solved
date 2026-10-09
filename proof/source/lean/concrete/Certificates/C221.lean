import Inputs.C221
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C221
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 221) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 221)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3816), (1, 976), (2, 2952), (3, 3397), (4, 2690), (5, 3649), (6, 2091), (7, 3095), (8, 1550), (9, 311), (10, 425), (11, 253)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 221) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 221) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 221) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C221
