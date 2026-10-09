import Inputs.C088
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C088
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 88) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 88)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2432), (1, 3392), (2, 1984), (3, 3520), (4, 2624), (5, 3904), (6, 3134), (7, 2573), (8, 3631), (9, 436), (10, 366), (11, 507)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 88) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 88) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 88) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C088
