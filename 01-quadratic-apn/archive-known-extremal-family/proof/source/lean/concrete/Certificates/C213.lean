import Inputs.C213
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C213
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 213) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 213)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2736), (1, 1256), (2, 824), (3, 2438), (4, 3397), (5, 1991), (6, 562), (7, 2091), (8, 1084), (9, 101), (10, 306), (11, 153)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 213) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 213) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 213) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C213
