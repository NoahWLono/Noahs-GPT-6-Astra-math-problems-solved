import Inputs.C045
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C045
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 45) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 45)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3600), (1, 536), (2, 2592), (3, 4034), (4, 579), (5, 2884), (6, 1080), (7, 1544), (8, 2088), (9, 191), (10, 201), (11, 301)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 45) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 45) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 45) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C045
