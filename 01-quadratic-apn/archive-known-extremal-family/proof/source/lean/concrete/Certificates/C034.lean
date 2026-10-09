import Inputs.C034
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C034
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 34) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 34)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 176), (1, 232), (2, 312), (3, 6), (4, 5), (5, 7), (6, 3074), (7, 2563), (8, 3588), (9, 384), (10, 320), (11, 448)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 34) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 34) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 34) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C034
