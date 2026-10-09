import Inputs.C051
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C051
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 51) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 51)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 416), (1, 368), (2, 472), (3, 3076), (4, 2566), (5, 3587), (6, 6), (7, 5), (8, 7), (9, 48), (10, 40), (11, 56)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 51) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 51) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 51) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C051
