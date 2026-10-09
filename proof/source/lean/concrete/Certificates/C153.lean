import Inputs.C153
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C153
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 153) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 153)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3248), (1, 2792), (2, 3896), (3, 2374), (4, 3205), (5, 1607), (6, 554), (7, 2067), (8, 1036), (9, 102), (10, 309), (11, 159)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 153) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 153) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 153) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C153
