import Inputs.C175
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C175
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 175) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 175)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1840), (1, 4008), (2, 3320), (3, 2310), (4, 3461), (5, 1735), (6, 3108), (7, 2614), (8, 3611), (9, 419), (10, 375), (11, 478)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 175) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 175) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 175) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C175
