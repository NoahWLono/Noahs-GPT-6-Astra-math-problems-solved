import Inputs.C222
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C222
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 222) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 222)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 4008), (1, 848), (2, 3016), (3, 1861), (4, 3714), (5, 3137), (6, 2094), (7, 3093), (8, 1551), (9, 287), (10, 441), (11, 245)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 222) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 222) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 222) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C222
