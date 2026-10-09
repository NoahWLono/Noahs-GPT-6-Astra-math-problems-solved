import Inputs.C220
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C220
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 220) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 220)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1344), (1, 1664), (2, 2112), (3, 2816), (4, 1408), (5, 704), (6, 1573), (7, 3634), (8, 3097), (9, 234), (10, 467), (11, 396)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 220) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 220) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 220) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C220
