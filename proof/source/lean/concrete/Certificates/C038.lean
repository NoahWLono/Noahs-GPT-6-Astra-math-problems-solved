import Inputs.C038
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C038
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 38) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 38)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 176), (1, 232), (2, 312), (3, 134), (4, 197), (5, 263), (6, 3090), (7, 2587), (8, 3620), (9, 384), (10, 320), (11, 448)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 38) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 38) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 38) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C038
