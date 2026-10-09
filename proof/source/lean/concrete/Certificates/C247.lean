import Inputs.C247
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C247
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 247) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 247)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3160), (1, 2872), (2, 3760), (3, 771), (4, 2439), (5, 1222), (6, 33), (7, 52), (8, 26), (9, 14), (10, 37), (11, 23)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 247) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 247) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 247) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C247
