import Inputs.C029
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C029
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 29) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 29)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3960), (1, 648), (2, 2664), (3, 1479), (4, 1601), (5, 2373), (6, 1085), (7, 1546), (8, 2089), (9, 151), (10, 217), (11, 293)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 29) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 29) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 29) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C029
