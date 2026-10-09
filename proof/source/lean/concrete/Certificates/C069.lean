import Inputs.C069
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C069
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 69) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 69)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2608), (1, 1064), (2, 568), (3, 3270), (4, 3013), (5, 3975), (6, 3096), (7, 2616), (8, 3632), (9, 437), (10, 362), (11, 505)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 69) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 69) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 69) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C069
