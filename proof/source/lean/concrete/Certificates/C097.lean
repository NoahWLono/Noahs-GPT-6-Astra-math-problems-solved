import Inputs.C097
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C097
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 97) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 97)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2568), (1, 1056), (2, 528), (3, 3393), (4, 2692), (5, 3650), (6, 552), (7, 2064), (8, 1032), (9, 117), (10, 298), (11, 185)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 97) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 97) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 97) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C097
