import Inputs.C079
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C079
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 79) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 79)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2240), (1, 3520), (2, 1920), (3, 1792), (4, 3968), (5, 3264), (6, 35), (7, 55), (8, 30), (9, 28), (10, 62), (11, 51)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 79) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 79) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 79) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C079
