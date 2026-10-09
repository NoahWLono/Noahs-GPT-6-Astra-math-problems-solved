import Inputs.C219
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C219
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 219) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 219)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1792), (1, 3968), (2, 3264), (3, 2048), (4, 3072), (5, 1536), (6, 3588), (7, 518), (8, 2563), (9, 483), (10, 119), (11, 350)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 219) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 219) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 219) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C219
