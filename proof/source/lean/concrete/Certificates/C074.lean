import Inputs.C074
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C074
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 74) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 74)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1968), (1, 3944), (2, 3576), (3, 326), (4, 133), (5, 71), (6, 3118), (7, 2581), (8, 3599), (9, 387), (10, 327), (11, 454)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 74) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 74) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 74) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C074
