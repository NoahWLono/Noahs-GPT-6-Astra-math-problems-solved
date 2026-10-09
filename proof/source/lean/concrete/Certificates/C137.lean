import Inputs.C137
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C137
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 137) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 137)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2464), (1, 3440), (2, 2008), (3, 1412), (4, 1862), (5, 2499), (6, 2102), (7, 3117), (8, 1599), (9, 276), (10, 414), (11, 227)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 137) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 137) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 137) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C137
