import Inputs.C177
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C177
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 177) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 177)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 376), (1, 136), (2, 104), (3, 903), (4, 2369), (5, 1477), (6, 2101), (7, 3114), (8, 1593), (9, 264), (10, 416), (11, 208)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 177) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 177) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 177) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C177
