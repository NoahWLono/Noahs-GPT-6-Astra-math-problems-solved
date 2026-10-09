import Inputs.C187
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C187
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 187) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 187)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2136), (1, 3384), (2, 1712), (3, 899), (4, 2375), (5, 1478), (6, 49), (7, 44), (8, 58), (9, 12), (10, 38), (11, 19)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 187) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 187) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 187) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C187
