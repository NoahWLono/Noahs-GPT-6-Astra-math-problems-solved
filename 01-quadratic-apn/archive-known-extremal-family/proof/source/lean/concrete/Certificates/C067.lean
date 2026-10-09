import Inputs.C067
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C067
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 67) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 67)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3328), (1, 2944), (2, 3776), (3, 2432), (4, 3392), (5, 1984), (6, 52), (7, 46), (8, 59), (9, 38), (10, 53), (11, 31)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 67) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 67) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 67) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C067
