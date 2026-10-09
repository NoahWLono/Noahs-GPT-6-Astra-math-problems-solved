import Inputs.C018
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C018
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 18) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 18)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 400), (1, 344), (2, 480), (3, 2050), (4, 3075), (5, 1540), (6, 3078), (7, 2565), (8, 3591), (9, 416), (10, 368), (11, 472)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 18) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 18) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 18) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C018
