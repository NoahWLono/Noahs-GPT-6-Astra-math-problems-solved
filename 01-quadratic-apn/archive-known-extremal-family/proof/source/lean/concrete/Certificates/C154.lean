import Inputs.C154
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C154
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 154) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 154)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3376), (1, 2984), (2, 3832), (3, 1350), (4, 1669), (5, 2119), (6, 556), (7, 2070), (8, 1035), (9, 86), (10, 285), (11, 167)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 154) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 154) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 154) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C154
