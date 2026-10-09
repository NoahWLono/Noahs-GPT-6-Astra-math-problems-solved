import Inputs.C178
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C178
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 178) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 178)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 120), (1, 264), (2, 168), (3, 2951), (4, 1345), (5, 965), (6, 2097), (7, 3116), (8, 1594), (9, 296), (10, 400), (11, 200)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 178) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 178) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 178) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C178
