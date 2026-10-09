import Inputs.C143
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C143
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 143) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 143)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3008), (1, 1088), (2, 832), (3, 4032), (4, 576), (5, 2880), (6, 63), (7, 9), (8, 45), (9, 61), (10, 10), (11, 41)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 143) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 143) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 143) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C143
