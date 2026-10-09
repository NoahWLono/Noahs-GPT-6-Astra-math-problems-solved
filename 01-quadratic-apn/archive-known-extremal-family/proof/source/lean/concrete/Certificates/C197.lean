import Inputs.C197
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C197
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 197) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 197)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3488), (1, 2928), (2, 4056), (3, 1284), (4, 1926), (5, 2243), (6, 2086), (7, 3125), (8, 1567), (9, 278), (10, 413), (11, 231)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 197) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 197) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 197) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C197
