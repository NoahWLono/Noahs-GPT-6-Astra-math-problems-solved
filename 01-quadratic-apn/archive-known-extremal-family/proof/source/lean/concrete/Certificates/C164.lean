import Inputs.C164
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C164
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 164) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 164)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 136), (1, 224), (2, 272), (3, 1473), (4, 1604), (5, 2370), (6, 570), (7, 2059), (8, 1068), (9, 80), (10, 280), (11, 160)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 164) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 164) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 164) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C164
