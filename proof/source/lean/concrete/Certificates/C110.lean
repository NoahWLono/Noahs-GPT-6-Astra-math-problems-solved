import Inputs.C110
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C110
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 110) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 110)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3936), (1, 688), (2, 2648), (3, 452), (4, 70), (5, 323), (6, 2109), (7, 3082), (8, 1577), (9, 263), (10, 385), (11, 197)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 110) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 110) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 110) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C110
