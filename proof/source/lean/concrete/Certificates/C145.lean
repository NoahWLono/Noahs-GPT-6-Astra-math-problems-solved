import Inputs.C145
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C145
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 145) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 145)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 352), (1, 176), (2, 88), (3, 900), (4, 2374), (5, 1475), (6, 3637), (7, 554), (8, 2617), (9, 456), (10, 96), (11, 336)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 145) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 145) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 145) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C145
