import Inputs.C111
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C111
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 111) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 111)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3912), (1, 672), (2, 2640), (3, 3009), (4, 1092), (5, 834), (6, 573), (7, 2058), (8, 1065), (9, 111), (10, 273), (11, 141)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 111) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 111) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 111) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C111
