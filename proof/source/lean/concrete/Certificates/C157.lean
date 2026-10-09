import Inputs.C157
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C157
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 157) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 157)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2792), (1, 1488), (2, 904), (3, 3525), (4, 2626), (5, 3905), (6, 2107), (7, 3087), (8, 1582), (9, 309), (10, 426), (11, 249)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 157) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 157) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 157) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C157
