import Inputs.C044
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C044
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 44) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 44)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1056), (1, 1584), (2, 2072), (3, 132), (4, 198), (5, 259), (6, 2064), (7, 3096), (8, 1568), (9, 258), (10, 387), (11, 196)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 44) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 44) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 44) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C044
