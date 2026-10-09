import Inputs.C183
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C183
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 183) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 183)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 312), (1, 392), (2, 232), (3, 2247), (4, 3521), (5, 1925), (6, 28), (7, 62), (8, 51), (9, 32), (10, 48), (11, 24)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 183) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 183) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 183) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C183
