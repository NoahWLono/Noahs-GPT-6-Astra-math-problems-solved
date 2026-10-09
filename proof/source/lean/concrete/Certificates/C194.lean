import Inputs.C194
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C194
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 194) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 194)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2800), (1, 1512), (2, 952), (3, 2566), (4, 1029), (5, 519), (6, 3075), (7, 2567), (8, 3590), (9, 429), (10, 338), (11, 457)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 194) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 194) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 194) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C194
