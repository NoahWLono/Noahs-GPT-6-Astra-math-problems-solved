import Inputs.C245
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C245
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 245) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 245)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2696), (1, 1248), (2, 784), (3, 2433), (4, 3396), (5, 1986), (6, 3122), (7, 2603), (8, 3644), (9, 421), (10, 370), (11, 473)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 245) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 245) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 245) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C245
