import Inputs.C099
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C099
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 99) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 99)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3000), (1, 1352), (2, 1000), (3, 3399), (4, 2689), (5, 3653), (6, 3630), (7, 533), (8, 2575), (9, 501), (10, 106), (11, 377)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 99) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 99) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 99) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C099
