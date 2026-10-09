import Inputs.C210
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C210
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 210) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 210)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3168), (1, 2864), (2, 3736), (3, 2564), (4, 1030), (5, 515), (6, 3585), (7, 516), (8, 2562), (9, 494), (10, 85), (11, 335)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 210) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 210) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 210) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C210
