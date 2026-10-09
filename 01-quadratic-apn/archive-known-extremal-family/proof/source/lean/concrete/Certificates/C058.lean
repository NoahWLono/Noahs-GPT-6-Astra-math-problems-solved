import Inputs.C058
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C058
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 58) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 58)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1456), (1, 1896), (2, 2552), (3, 2054), (4, 3077), (5, 1543), (6, 1030), (7, 1541), (8, 2055), (9, 162), (10, 243), (11, 284)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 58) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 58) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 58) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C058
