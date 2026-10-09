import Inputs.C073
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C073
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 73) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 73)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1584), (1, 3624), (2, 3128), (3, 3398), (4, 2693), (5, 3655), (6, 3112), (7, 2576), (8, 3592), (9, 435), (10, 367), (11, 510)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 73) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 73) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 73) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C073
