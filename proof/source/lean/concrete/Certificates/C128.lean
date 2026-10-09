import Inputs.C128
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C128
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 128) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 128)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 448), (1, 64), (2, 320), (3, 4032), (4, 576), (5, 2880), (6, 63), (7, 9), (8, 45), (9, 56), (10, 8), (11, 40)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 128) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 128) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 128) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C128
