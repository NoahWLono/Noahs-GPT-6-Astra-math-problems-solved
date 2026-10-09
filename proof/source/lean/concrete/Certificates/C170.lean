import Inputs.C170
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C170
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 170) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 170)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3272), (1, 3040), (2, 3984), (3, 2881), (4, 1156), (5, 578), (6, 555), (7, 2071), (8, 1038), (9, 110), (10, 277), (11, 143)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 170) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 170) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 170) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C170
