import Inputs.C046
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C046
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 46) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 46)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 4048), (1, 600), (2, 2912), (3, 450), (4, 67), (5, 324), (6, 1087), (7, 1545), (8, 2093), (9, 135), (10, 193), (11, 261)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 46) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 46) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 46) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C046
