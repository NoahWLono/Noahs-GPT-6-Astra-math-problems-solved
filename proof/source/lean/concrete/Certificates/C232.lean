import Inputs.C232
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C232
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 232) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 232)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3720), (1, 736), (2, 2832), (3, 1025), (4, 1540), (5, 2050), (6, 514), (7, 2051), (8, 1028), (9, 87), (10, 281), (11, 165)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 232) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 232) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 232) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C232
