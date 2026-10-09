import Inputs.C043
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C043
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 43) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 43)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1184), (1, 1776), (2, 2328), (3, 1028), (4, 1542), (5, 2051), (6, 2050), (7, 3075), (8, 1540), (9, 274), (10, 411), (11, 228)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 43) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 43) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 43) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C043
