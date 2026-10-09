import Inputs.C253
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C253
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 253) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 253)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3808), (1, 1008), (2, 2968), (3, 3396), (4, 2694), (5, 3651), (6, 2603), (7, 1047), (8, 526), (9, 375), (10, 169), (11, 125)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 253) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 253) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 253) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C253
