import Inputs.C115
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C115
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 115) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 115)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2680), (1, 1288), (2, 680), (3, 839), (4, 2177), (5, 1093), (6, 41), (7, 20), (8, 10), (9, 13), (10, 34), (11, 17)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 115) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 115) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 115) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C115
