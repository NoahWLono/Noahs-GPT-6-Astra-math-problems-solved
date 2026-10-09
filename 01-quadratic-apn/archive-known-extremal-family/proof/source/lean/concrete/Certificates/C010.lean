import Inputs.C010
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C010
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 10) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 10)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 584), (1, 2336), (2, 1168), (3, 1), (4, 4), (5, 2), (6, 513), (7, 2052), (8, 1026), (9, 65), (10, 260), (11, 130)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 10) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 10) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 10) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C010
