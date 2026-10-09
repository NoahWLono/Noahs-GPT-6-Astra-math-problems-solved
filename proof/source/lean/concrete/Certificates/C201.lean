import Inputs.C201
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C201
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 201) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 201)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1904), (1, 3752), (2, 3192), (3, 1542), (4, 3589), (5, 3079), (6, 3077), (7, 2562), (8, 3585), (9, 411), (10, 383), (11, 502)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 201) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 201) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 201) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C201
