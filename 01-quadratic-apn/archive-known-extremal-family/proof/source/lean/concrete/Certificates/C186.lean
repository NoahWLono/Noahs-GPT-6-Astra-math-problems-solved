import Inputs.C186
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C186
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 186) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 186)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3336), (1, 2976), (2, 3792), (3, 1345), (4, 1668), (5, 2114), (6, 3116), (7, 2582), (8, 3595), (9, 406), (10, 349), (11, 487)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 186) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 186) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 186) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C186
