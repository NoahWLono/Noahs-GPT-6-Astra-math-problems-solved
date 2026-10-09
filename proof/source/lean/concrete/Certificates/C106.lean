import Inputs.C106
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C106
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 106) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 106)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1336), (1, 1928), (2, 2280), (3, 391), (4, 321), (5, 453), (6, 3636), (7, 558), (8, 2619), (9, 450), (10, 67), (11, 324)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 106) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 106) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 106) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C106
