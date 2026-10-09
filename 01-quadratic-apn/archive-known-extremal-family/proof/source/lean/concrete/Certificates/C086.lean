import Inputs.C086
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C086
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 86) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 86)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3552), (1, 2672), (2, 3928), (3, 1668), (4, 3782), (5, 3331), (6, 3607), (7, 537), (8, 2597), (9, 478), (10, 125), (11, 375)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 86) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 86) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 86) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C086
