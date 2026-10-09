import Inputs.C225
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C225
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 225) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 225)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3512), (1, 2888), (2, 4072), (3, 1031), (4, 1537), (5, 2053), (6, 3590), (7, 517), (8, 2567), (9, 470), (10, 93), (11, 359)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 225) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 225) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 225) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C225
