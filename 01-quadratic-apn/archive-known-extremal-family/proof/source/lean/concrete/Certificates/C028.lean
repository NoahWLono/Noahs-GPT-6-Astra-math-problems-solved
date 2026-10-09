import Inputs.C028
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C028
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 28) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 28)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1280), (1, 1920), (2, 2240), (3, 2176), (4, 3264), (5, 1792), (6, 2068), (7, 3102), (8, 1571), (9, 290), (10, 435), (11, 220)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 28) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 28) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 28) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C028
