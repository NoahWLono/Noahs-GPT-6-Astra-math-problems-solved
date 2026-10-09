import Inputs.C033
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C033
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 33) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 33)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 48), (1, 40), (2, 56), (3, 1030), (4, 1541), (5, 2055), (6, 3072), (7, 2560), (8, 3584), (9, 400), (10, 344), (11, 480)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 33) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 33) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 33) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C033
