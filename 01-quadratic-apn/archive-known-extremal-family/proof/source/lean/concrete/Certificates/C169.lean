import Inputs.C169
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C169
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 169) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 169)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3400), (1, 2720), (2, 3664), (3, 1857), (4, 3716), (5, 3138), (6, 557), (7, 2066), (8, 1033), (9, 94), (10, 317), (11, 183)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 169) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 169) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 169) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C169
