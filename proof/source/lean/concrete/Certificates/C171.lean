import Inputs.C171
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C171
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 171) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 171)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2200), (1, 3320), (2, 1840), (3, 1411), (4, 1863), (5, 2502), (6, 1586), (7, 3627), (8, 3132), (9, 212), (10, 478), (11, 419)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 171) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 171) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 171) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C171
