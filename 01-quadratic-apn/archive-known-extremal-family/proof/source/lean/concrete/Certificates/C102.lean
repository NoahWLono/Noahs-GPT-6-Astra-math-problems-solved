import Inputs.C102
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C102
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 102) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 102)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3384), (1, 2952), (2, 3816), (3, 135), (4, 193), (5, 261), (6, 3604), (7, 542), (8, 2595), (9, 454), (10, 69), (11, 327)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 102) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 102) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 102) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C102
