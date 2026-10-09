import Inputs.C214
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C214
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 214) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 214)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2864), (1, 1448), (2, 760), (3, 1414), (4, 1861), (5, 2503), (6, 564), (7, 2094), (8, 1083), (9, 85), (10, 282), (11, 161)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 214) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 214) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 214) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C214
