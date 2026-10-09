import Inputs.C125
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C125
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 125) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 125)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3680), (1, 816), (2, 2712), (3, 2500), (4, 3142), (5, 1859), (6, 2617), (7, 1036), (8, 554), (9, 359), (10, 177), (11, 93)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 125) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 125) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 125) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C125
