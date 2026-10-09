import Inputs.C162
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C162
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 162) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 162)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 184), (1, 200), (2, 296), (3, 3463), (4, 2881), (5, 4037), (6, 3634), (7, 555), (8, 2620), (9, 496), (10, 104), (11, 376)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 162) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 162) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 162) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C162
