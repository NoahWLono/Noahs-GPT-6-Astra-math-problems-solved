import Inputs.C217
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C217
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 217) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 217)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1376), (1, 1712), (2, 2136), (3, 516), (4, 2054), (5, 1027), (6, 3589), (7, 514), (8, 2561), (9, 458), (10, 99), (11, 340)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 217) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 217) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 217) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C217
