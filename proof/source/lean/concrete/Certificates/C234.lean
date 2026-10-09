import Inputs.C234
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C234
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 234) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 234)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1208), (1, 1736), (2, 2344), (3, 3079), (4, 2561), (5, 3589), (6, 3586), (7, 515), (8, 2564), (9, 498), (10, 107), (11, 380)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 234) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 234) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 234) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C234
