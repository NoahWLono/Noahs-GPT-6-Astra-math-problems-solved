import Inputs.C224
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C224
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 224) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 224)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1160), (1, 1760), (2, 2320), (3, 1025), (4, 1540), (5, 2050), (6, 514), (7, 2051), (8, 1028), (9, 82), (10, 283), (11, 164)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 224) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 224) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 224) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C224
