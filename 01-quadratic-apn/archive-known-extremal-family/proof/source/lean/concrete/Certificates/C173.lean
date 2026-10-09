import Inputs.C173
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C173
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 173) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 173)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2720), (1, 1264), (2, 792), (3, 4036), (4, 582), (5, 2883), (6, 2106), (7, 3083), (8, 1580), (9, 317), (10, 394), (11, 233)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 173) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 173) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 173) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C173
