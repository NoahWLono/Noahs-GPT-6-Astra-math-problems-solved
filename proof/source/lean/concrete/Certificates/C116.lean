import Inputs.C116
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C116
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 116) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 116)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 4016), (1, 872), (2, 3064), (3, 3334), (4, 2949), (5, 3783), (6, 38), (7, 53), (8, 31), (9, 55), (10, 41), (11, 61)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 116) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 116) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 116) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C116
