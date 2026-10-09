import Inputs.C231
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C231
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 231) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 231)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3224), (1, 2808), (2, 3888), (3, 1283), (4, 1927), (5, 2246), (6, 1570), (7, 3635), (8, 3100), (9, 214), (10, 477), (11, 423)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 231) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 231) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 231) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C231
