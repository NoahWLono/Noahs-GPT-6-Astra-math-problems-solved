import Inputs.C140
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C140
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 140) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 140)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3392), (1, 2688), (2, 3648), (3, 2752), (4, 1472), (5, 896), (6, 29), (7, 58), (8, 49), (9, 46), (10, 21), (11, 15)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 140) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 140) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 140) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C140
