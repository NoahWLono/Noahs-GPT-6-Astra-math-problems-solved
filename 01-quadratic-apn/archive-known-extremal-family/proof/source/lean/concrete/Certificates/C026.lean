import Inputs.C026
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C026
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 26) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 26)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1424), (1, 1880), (2, 2528), (3, 2050), (4, 3075), (5, 1540), (6, 3078), (7, 2565), (8, 3591), (9, 418), (10, 371), (11, 476)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 26) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 26) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 26) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C026
