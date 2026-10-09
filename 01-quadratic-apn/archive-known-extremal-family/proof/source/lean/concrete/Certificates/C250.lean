import Inputs.C250
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C250
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 250) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 250)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1144), (1, 1800), (2, 2216), (3, 2567), (4, 1025), (5, 517), (6, 2049), (7, 3076), (8, 1538), (9, 298), (10, 403), (11, 204)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 250) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 250) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 250) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C250
