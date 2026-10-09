import Inputs.C030
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C030
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 30) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 30)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3768), (1, 712), (2, 2856), (3, 3015), (4, 1089), (5, 837), (6, 1082), (7, 1547), (8, 2092), (9, 175), (10, 209), (11, 269)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 30) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 30) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 30) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C030
