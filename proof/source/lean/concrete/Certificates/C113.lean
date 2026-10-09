import Inputs.C113
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C113
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 113) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 113)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3016), (1, 1120), (2, 848), (3, 833), (4, 2180), (5, 1090), (6, 3119), (7, 2577), (8, 3597), (9, 397), (10, 354), (11, 465)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 113) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 113) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 113) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C113
