import Inputs.C239
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C239
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 239) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 239)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2352), (1, 3496), (2, 1784), (3, 2246), (4, 3525), (5, 1927), (6, 3100), (7, 2622), (8, 3635), (9, 420), (10, 374), (11, 475)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 239) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 239) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 239) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C239
