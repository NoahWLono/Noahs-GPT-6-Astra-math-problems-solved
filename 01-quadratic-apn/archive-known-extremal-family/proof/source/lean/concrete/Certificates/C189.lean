import Inputs.C189
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C189
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 189) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 189)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2784), (1, 1520), (2, 920), (3, 3524), (4, 2630), (5, 3907), (6, 2619), (7, 1039), (8, 558), (9, 373), (10, 170), (11, 121)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 189) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 189) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 189) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C189
