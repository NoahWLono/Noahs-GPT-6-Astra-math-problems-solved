import Inputs.C176
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C176
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 176) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 176)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 200), (1, 480), (2, 400), (3, 1665), (4, 3780), (5, 3330), (6, 19), (7, 31), (8, 38), (9, 24), (10, 56), (11, 48)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 176) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 176) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 176) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C176
