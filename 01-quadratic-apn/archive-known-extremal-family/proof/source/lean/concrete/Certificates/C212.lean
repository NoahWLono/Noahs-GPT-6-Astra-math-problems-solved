import Inputs.C212
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C212
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 212) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 212)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3648), (1, 768), (2, 2688), (3, 704), (4, 2496), (5, 1408), (6, 3097), (7, 2620), (8, 3634), (9, 399), (10, 353), (11, 469)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 212) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 212) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 212) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C212
