import Inputs.C012
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C012
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 12) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 12)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 512), (1, 2048), (2, 1024), (3, 64), (4, 256), (5, 128), (6, 8), (7, 32), (8, 16), (9, 1), (10, 4), (11, 2)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 12) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 12) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 12) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C012
