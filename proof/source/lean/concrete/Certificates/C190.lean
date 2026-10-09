import Inputs.C190
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C190
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 190) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 190)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2976), (1, 1392), (2, 984), (3, 1988), (4, 3654), (5, 3395), (6, 2622), (7, 1037), (8, 559), (9, 349), (10, 186), (11, 113)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 190) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 190) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 190) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C190
