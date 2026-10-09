import Inputs.C009
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C009
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 9) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 9)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 520), (1, 2080), (2, 1040), (3, 513), (4, 2052), (5, 1026), (6, 512), (7, 2048), (8, 1024), (9, 73), (10, 292), (11, 146)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 9) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 9) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 9) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C009
