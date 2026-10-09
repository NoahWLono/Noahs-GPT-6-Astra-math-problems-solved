import Inputs.C092
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C092
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 92) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 92)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1984), (1, 3648), (2, 3392), (3, 3776), (4, 960), (5, 2944), (6, 3615), (7, 569), (8, 2613), (9, 507), (10, 79), (11, 366)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 92) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 92) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 92) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C092
