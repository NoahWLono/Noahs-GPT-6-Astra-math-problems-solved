import Inputs.C158
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C158
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 158) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 158)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2984), (1, 1360), (2, 968), (3, 1989), (4, 3650), (5, 3393), (6, 2110), (7, 3085), (8, 1583), (9, 285), (10, 442), (11, 241)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 158) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 158) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 158) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C158
