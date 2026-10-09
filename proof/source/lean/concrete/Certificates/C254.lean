import Inputs.C254
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C254
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 254) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 254)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 4000), (1, 880), (2, 3032), (3, 1860), (4, 3718), (5, 3139), (6, 2606), (7, 1045), (8, 527), (9, 351), (10, 185), (11, 117)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 254) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 254) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 254) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C254
