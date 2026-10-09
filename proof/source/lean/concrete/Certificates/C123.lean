import Inputs.C123
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C123
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 123) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 123)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1496), (1, 1656), (2, 2416), (3, 3971), (4, 839), (5, 3014), (6, 55), (7, 41), (8, 61), (9, 58), (10, 11), (11, 44)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 123) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 123) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 123) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C123
