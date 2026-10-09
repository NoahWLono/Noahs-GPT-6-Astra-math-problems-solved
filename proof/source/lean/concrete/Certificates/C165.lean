import Inputs.C165
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C165
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 165) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 165)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 440), (1, 328), (2, 488), (3, 1159), (4, 1729), (5, 2309), (6, 3606), (7, 541), (8, 2599), (9, 464), (10, 88), (11, 352)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 165) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 165) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 165) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C165
