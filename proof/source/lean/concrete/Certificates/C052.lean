import Inputs.C052
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C052
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 52) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 52)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 360), (1, 144), (2, 72), (3, 3013), (4, 1090), (5, 833), (6, 61), (7, 10), (8, 41), (9, 40), (10, 16), (11, 8)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 52) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 52) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 52) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C052
