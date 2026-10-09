import Inputs.C230
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C230
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 230) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 230)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2760), (1, 1504), (2, 912), (3, 2945), (4, 1348), (5, 962), (6, 563), (7, 2095), (8, 1086), (9, 109), (10, 274), (11, 137)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 230) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 230) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 230) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C230
