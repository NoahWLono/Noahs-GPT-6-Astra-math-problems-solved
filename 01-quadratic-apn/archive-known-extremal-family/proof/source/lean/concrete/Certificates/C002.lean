import Inputs.C002
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C002
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 2) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 2)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 72), (1, 288), (2, 144), (3, 1), (4, 4), (5, 2), (6, 513), (7, 2052), (8, 1026), (9, 64), (10, 256), (11, 128)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 2) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 2) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 2) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C002
