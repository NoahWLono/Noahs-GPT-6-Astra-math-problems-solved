import Inputs.C100
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C100
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 100) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 100)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3632), (1, 552), (2, 2616), (3, 262), (4, 389), (5, 199), (6, 3104), (7, 2608), (8, 3608), (9, 391), (10, 321), (11, 453)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 100) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 100) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 100) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C100
