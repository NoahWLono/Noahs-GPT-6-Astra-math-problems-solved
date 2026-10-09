import Inputs.C243
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C243
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 243) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 243)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2872), (1, 1416), (2, 744), (3, 2055), (4, 3073), (5, 1541), (6, 4), (7, 6), (8, 3), (9, 37), (10, 50), (11, 25)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 243) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 243) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 243) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C243
