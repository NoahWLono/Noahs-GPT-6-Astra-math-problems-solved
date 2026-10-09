import Inputs.C061
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C061
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 61) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 61)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3920), (1, 664), (2, 2656), (3, 1474), (4, 1603), (5, 2372), (6, 3645), (7, 522), (8, 2601), (9, 471), (10, 89), (11, 357)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 61) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 61) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 61) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C061
