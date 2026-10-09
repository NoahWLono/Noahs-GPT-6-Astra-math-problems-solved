import Inputs.C005
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C005
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 5) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 5)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 8), (1, 32), (2, 16), (3, 577), (4, 2308), (5, 1154), (6, 520), (7, 2080), (8, 1040), (9, 72), (10, 288), (11, 144)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 5) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 5) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 5) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C005
