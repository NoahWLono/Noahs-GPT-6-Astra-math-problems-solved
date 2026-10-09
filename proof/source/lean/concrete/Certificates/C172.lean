import Inputs.C172
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C172
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 172) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 172)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2456), (1, 3448), (2, 2032), (3, 3203), (4, 2759), (5, 3846), (6, 1558), (7, 3613), (8, 3111), (9, 244), (10, 494), (11, 443)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 172) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 172) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 172) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C172
