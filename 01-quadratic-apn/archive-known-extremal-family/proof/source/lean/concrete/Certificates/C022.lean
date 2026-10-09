import Inputs.C022
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C022
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 22) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 22)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 400), (1, 344), (2, 480), (3, 2178), (4, 3267), (5, 1796), (6, 3094), (7, 2589), (8, 3623), (9, 416), (10, 368), (11, 472)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 22) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 22) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 22) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C022
