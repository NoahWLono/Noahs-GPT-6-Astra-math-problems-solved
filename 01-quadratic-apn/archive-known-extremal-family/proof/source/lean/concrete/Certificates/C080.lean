import Inputs.C080
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C080
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 80) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 80)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1088), (1, 1792), (2, 2176), (3, 640), (4, 2240), (5, 1280), (6, 529), (7, 2076), (8, 1058), (9, 74), (10, 291), (11, 148)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 80) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 80) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 80) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C080
