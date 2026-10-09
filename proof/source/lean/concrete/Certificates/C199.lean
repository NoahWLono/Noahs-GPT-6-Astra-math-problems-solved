import Inputs.C199
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C199
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 199) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 199)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2752), (1, 1472), (2, 896), (3, 1920), (4, 3904), (5, 3520), (6, 51), (7, 47), (8, 62), (9, 29), (10, 58), (11, 49)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 199) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 199) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 199) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C199
