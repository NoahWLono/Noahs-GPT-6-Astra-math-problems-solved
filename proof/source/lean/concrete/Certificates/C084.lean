import Inputs.C084
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C084
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 84) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 84)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3968), (1, 832), (2, 3008), (3, 3328), (4, 2944), (5, 3776), (6, 3110), (7, 2613), (8, 3615), (9, 439), (10, 361), (11, 509)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 84) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 84) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 84) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C084
