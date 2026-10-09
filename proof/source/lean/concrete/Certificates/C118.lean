import Inputs.C118
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C118
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 118) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 118)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3576), (1, 2632), (2, 3944), (3, 1671), (4, 3777), (5, 3333), (6, 2071), (7, 3097), (8, 1573), (9, 286), (10, 445), (11, 247)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 118) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 118) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 118) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C118
