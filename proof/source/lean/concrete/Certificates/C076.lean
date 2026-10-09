import Inputs.C076
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C076
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 76) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 76)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1024), (1, 1536), (2, 2048), (3, 128), (4, 192), (5, 256), (6, 16), (7, 24), (8, 32), (9, 2), (10, 3), (11, 4)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 76) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 76) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 76) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C076
