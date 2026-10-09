import Inputs.C192
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C192
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 192) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 192)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 4032), (1, 576), (2, 2880), (3, 3584), (4, 512), (5, 2560), (6, 7), (7, 1), (8, 5), (9, 63), (10, 9), (11, 45)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 192) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 192) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 192) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C192
