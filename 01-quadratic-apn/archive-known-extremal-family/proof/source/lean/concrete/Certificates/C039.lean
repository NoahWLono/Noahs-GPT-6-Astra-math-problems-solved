import Inputs.C039
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C039
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 39) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 39)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 160), (1, 240), (2, 280), (3, 1156), (4, 1734), (5, 2307), (6, 2066), (7, 3099), (8, 1572), (9, 272), (10, 408), (11, 224)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 39) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 39) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 39) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C039
