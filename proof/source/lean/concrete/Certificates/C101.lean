import Inputs.C101
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C101
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 101) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 101)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3128), (1, 2568), (2, 3624), (3, 2183), (4, 3265), (5, 1797), (6, 3600), (7, 536), (8, 2592), (9, 486), (10, 117), (11, 351)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 101) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 101) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 101) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C101
