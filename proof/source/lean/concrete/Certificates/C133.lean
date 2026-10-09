import Inputs.C133
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C133
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 133) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 133)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 368), (1, 168), (2, 120), (3, 1734), (4, 4037), (5, 3463), (6, 3101), (7, 2618), (8, 3633), (9, 408), (10, 376), (11, 496)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 133) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 133) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 133) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C133
