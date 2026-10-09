import Inputs.C209
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C209
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 209) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 209)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3424), (1, 2736), (2, 3672), (3, 516), (4, 2054), (5, 1027), (6, 3589), (7, 514), (8, 2561), (9, 462), (10, 101), (11, 343)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 209) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 209) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 209) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C209
