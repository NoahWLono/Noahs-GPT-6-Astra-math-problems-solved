import Inputs.C198
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C198
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 198) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 198)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3232), (1, 2800), (2, 3864), (3, 3332), (4, 2950), (5, 3779), (6, 2082), (7, 3123), (8, 1564), (9, 310), (10, 429), (11, 255)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 198) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 198) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 198) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C198
