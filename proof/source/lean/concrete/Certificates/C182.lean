import Inputs.C182
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C182
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 182) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 182)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 120), (1, 264), (2, 168), (3, 2695), (4, 1217), (5, 773), (6, 2065), (7, 3100), (8, 1570), (9, 296), (10, 400), (11, 200)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 182) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 182) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 182) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C182
