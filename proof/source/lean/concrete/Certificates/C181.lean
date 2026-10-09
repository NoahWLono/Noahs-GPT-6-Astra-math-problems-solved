import Inputs.C181
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C181
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 181) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 181)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 376), (1, 136), (2, 104), (3, 647), (4, 2241), (5, 1285), (6, 2069), (7, 3098), (8, 1569), (9, 264), (10, 416), (11, 208)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 181) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 181) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 181) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C181
