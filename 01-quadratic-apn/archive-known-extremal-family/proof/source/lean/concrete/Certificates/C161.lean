import Inputs.C161
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C161
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 161) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 161)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 440), (1, 328), (2, 488), (3, 1415), (4, 1857), (5, 2501), (6, 3638), (7, 557), (8, 2623), (9, 464), (10, 88), (11, 352)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 161) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 161) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 161) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C161
