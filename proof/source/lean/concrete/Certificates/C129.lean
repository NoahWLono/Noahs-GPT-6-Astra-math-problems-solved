import Inputs.C129
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C129
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 129) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 129)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 368), (1, 168), (2, 120), (3, 1862), (4, 3717), (5, 3143), (6, 3117), (7, 2578), (8, 3593), (9, 408), (10, 376), (11, 496)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 129) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 129) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 129) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C129
