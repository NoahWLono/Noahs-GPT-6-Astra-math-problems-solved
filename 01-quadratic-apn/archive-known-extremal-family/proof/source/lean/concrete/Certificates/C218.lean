import Inputs.C218
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C218
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 218) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 218)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1120), (1, 1840), (2, 2200), (3, 2564), (4, 1030), (5, 515), (6, 3585), (7, 516), (8, 2562), (9, 490), (10, 83), (11, 332)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 218) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 218) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 218) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C218
