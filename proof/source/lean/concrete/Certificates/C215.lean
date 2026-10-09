import Inputs.C215
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C215
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 215) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 215)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3136), (1, 2816), (2, 3712), (3, 768), (4, 2432), (5, 1216), (6, 1569), (7, 3636), (8, 3098), (9, 206), (10, 485), (11, 407)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 215) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 215) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 215) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C215
