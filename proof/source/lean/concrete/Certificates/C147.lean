import Inputs.C147
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C147
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 147) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 147)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 256), (1, 384), (2, 192), (3, 2368), (4, 3200), (5, 1600), (6, 3628), (7, 534), (8, 2571), (9, 480), (10, 112), (11, 344)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 147) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 147) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 147) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C147
