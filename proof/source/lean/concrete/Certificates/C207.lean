import Inputs.C207
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C207
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 207) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 207)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 4032), (1, 576), (2, 2880), (3, 3904), (4, 640), (5, 2624), (6, 47), (7, 17), (8, 13), (9, 63), (10, 9), (11, 45)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 207) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 207) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 207) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C207
