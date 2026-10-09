import Inputs.C027
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C027
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 27) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 27)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1408), (1, 1856), (2, 2496), (3, 3072), (4, 2560), (5, 3584), (6, 2054), (7, 3077), (8, 1543), (9, 306), (10, 427), (11, 252)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 27) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 27) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 27) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C027
