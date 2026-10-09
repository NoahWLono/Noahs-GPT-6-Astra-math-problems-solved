import Inputs.C229
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C229
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 229) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 229)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2888), (1, 1184), (2, 592), (3, 1921), (4, 3908), (5, 3522), (6, 565), (7, 2090), (8, 1081), (9, 93), (10, 314), (11, 177)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 229) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 229) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 229) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C229
