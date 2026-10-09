import Inputs.C223
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C223
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 223) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 223)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2176), (1, 3264), (2, 1792), (3, 1216), (4, 1984), (5, 2432), (6, 3098), (7, 2619), (8, 3636), (9, 404), (10, 350), (11, 483)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 223) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 223) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 223) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C223
