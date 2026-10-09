import Inputs.C059
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C059
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 59) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 59)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1440), (1, 1904), (2, 2520), (3, 3076), (4, 2566), (5, 3587), (6, 6), (7, 5), (8, 7), (9, 50), (10, 43), (11, 60)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 59) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 59) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 59) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C059
