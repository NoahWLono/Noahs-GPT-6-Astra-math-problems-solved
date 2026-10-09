import Inputs.C121
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C121
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 121) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 121)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1272), (1, 1992), (2, 2472), (3, 3975), (4, 833), (5, 3013), (6, 2099), (7, 3119), (8, 1598), (9, 314), (10, 395), (11, 236)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 121) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 121) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 121) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C121
