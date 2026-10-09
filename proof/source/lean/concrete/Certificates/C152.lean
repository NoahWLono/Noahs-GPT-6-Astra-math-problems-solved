import Inputs.C152
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C152
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 152) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 152)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1600), (1, 3840), (2, 3200), (3, 960), (4, 2112), (5, 1344), (6, 3129), (7, 2572), (8, 3626), (9, 395), (10, 359), (11, 470)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 152) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 152) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 152) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C152
