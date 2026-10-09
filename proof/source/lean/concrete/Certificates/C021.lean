import Inputs.C021
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C021
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 21) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 21)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 272), (1, 408), (2, 224), (3, 3202), (4, 2755), (5, 3844), (6, 3092), (7, 2590), (8, 3619), (9, 432), (10, 360), (11, 504)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 21) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 21) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 21) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C021
