import Inputs.C146
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C146
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 146) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 146)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 96), (1, 304), (2, 152), (3, 2948), (4, 1350), (5, 963), (6, 3633), (7, 556), (8, 2618), (9, 488), (10, 80), (11, 328)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 146) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 146) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 146) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C146
