import Inputs.C082
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C082
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 82) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 82)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2672), (1, 1320), (2, 696), (3, 3910), (4, 645), (5, 2631), (6, 553), (7, 2068), (8, 1034), (9, 125), (10, 266), (11, 169)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 82) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 82) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 82) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C082
