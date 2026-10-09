import Inputs.C185
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C185
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 185) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 185)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3208), (1, 2784), (2, 3856), (3, 2369), (4, 3204), (5, 1602), (6, 3114), (7, 2579), (8, 3596), (9, 422), (10, 373), (11, 479)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 185) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 185) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 185) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C185
