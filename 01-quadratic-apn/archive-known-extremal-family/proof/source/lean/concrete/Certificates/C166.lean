import Inputs.C166
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C166
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 166) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 166)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 184), (1, 200), (2, 296), (3, 3207), (4, 2753), (5, 3845), (6, 3602), (7, 539), (8, 2596), (9, 496), (10, 104), (11, 376)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 166) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 166) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 166) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C166
