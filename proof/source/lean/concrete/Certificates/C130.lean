import Inputs.C130
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C130
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 130) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 130)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 240), (1, 488), (2, 440), (3, 2886), (4, 1157), (5, 583), (6, 3115), (7, 2583), (8, 3598), (9, 424), (10, 336), (11, 456)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 130) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 130) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 130) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C130
