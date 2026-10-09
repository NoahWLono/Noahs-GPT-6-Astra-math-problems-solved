import Inputs.C156
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C156
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 156) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 156)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2368), (1, 3200), (2, 1600), (3, 2688), (4, 1216), (5, 768), (6, 1557), (7, 3610), (8, 3105), (9, 236), (10, 470), (11, 395)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 156) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 156) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 156) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C156
