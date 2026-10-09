import Inputs.C070
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C070
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 70) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 70)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2992), (1, 1384), (2, 1016), (3, 198), (4, 453), (5, 391), (6, 3102), (7, 2621), (8, 3639), (9, 389), (10, 322), (11, 449)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 70) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 70) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 70) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C070
