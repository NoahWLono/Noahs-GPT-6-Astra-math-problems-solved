import Inputs.C108
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C108
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 108) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 108)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1592), (1, 3592), (2, 3112), (3, 199), (4, 449), (5, 389), (6, 3608), (7, 568), (8, 2608), (9, 451), (10, 71), (11, 326)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 108) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 108) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 108) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C108
