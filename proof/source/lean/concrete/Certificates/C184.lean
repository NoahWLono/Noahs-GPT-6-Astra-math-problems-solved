import Inputs.C184
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C184
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 184) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 184)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1648), (1, 3880), (2, 3256), (3, 966), (4, 2117), (5, 1351), (6, 57), (7, 12), (8, 42), (9, 11), (10, 39), (11, 22)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 184) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 184) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 184) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C184
