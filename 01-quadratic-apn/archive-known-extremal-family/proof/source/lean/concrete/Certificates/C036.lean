import Inputs.C036
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C036
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 36) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 36)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 40), (1, 16), (2, 8), (3, 453), (4, 66), (5, 321), (6, 2616), (7, 1032), (8, 552), (9, 320), (10, 128), (11, 64)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 36) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 36) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 36) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C036
