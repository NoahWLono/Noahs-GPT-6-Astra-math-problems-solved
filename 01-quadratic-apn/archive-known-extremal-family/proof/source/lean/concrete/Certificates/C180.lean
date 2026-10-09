import Inputs.C180
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C180
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 180) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 180)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 200), (1, 480), (2, 400), (3, 1985), (4, 3652), (5, 3394), (6, 59), (7, 15), (8, 46), (9, 24), (10, 56), (11, 48)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 180) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 180) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 180) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C180
