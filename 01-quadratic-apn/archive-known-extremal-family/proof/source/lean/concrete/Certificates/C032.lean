import Inputs.C032
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C032
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 32) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 32)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 40), (1, 16), (2, 8), (3, 5), (4, 2), (5, 1), (6, 2560), (7, 1024), (8, 512), (9, 320), (10, 128), (11, 64)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 32) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 32) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 32) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C032
