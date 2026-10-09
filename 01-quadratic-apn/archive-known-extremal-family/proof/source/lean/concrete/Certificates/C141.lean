import Inputs.C141
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C141
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 141) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 141)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2008), (1, 3704), (2, 3440), (3, 2307), (4, 3463), (5, 1734), (6, 1575), (7, 3633), (8, 3101), (9, 227), (10, 503), (11, 414)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 141) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 141) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 141) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C141
