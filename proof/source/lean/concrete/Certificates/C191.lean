import Inputs.C191
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C191
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 191) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 191)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1712), (1, 3816), (2, 3384), (3, 1286), (4, 1925), (5, 2247), (6, 34), (7, 51), (8, 28), (9, 19), (10, 31), (11, 38)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 191) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 191) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 191) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C191
