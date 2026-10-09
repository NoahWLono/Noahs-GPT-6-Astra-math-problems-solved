import Inputs.C104
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C104
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 104) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 104)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2096), (1, 3112), (2, 1592), (3, 454), (4, 69), (5, 327), (6, 3128), (7, 2568), (8, 3624), (9, 388), (10, 326), (11, 451)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 104) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 104) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 104) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C104
