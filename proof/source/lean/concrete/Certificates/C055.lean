import Inputs.C055
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C055
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 55) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 55)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 416), (1, 368), (2, 472), (3, 3204), (4, 2758), (5, 3843), (6, 22), (7, 29), (8, 39), (9, 48), (10, 40), (11, 56)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 55) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 55) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 55) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C055
