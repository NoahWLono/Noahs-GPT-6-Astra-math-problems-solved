import Inputs.C095
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C095
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 95) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 95)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3840), (1, 896), (2, 2752), (3, 2496), (4, 3136), (5, 1856), (6, 572), (7, 2062), (8, 1067), (9, 103), (10, 305), (11, 157)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 95) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 95) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 95) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C095
