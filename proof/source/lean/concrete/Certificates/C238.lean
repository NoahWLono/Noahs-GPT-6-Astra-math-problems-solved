import Inputs.C238
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C238
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 238) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 238)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 4064), (1, 624), (2, 2904), (3, 1348), (4, 1670), (5, 2115), (6, 2095), (7, 3089), (8, 1549), (9, 279), (10, 409), (11, 229)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 238) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 238) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 238) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C238
