import Inputs.C087
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C087
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 87) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 87)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3520), (1, 2624), (2, 3904), (3, 3712), (4, 704), (5, 2816), (6, 1559), (7, 3609), (8, 3109), (9, 254), (10, 461), (11, 431)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 87) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 87) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 87) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C087
