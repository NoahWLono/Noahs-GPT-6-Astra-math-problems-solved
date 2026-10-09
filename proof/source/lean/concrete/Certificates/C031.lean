import Inputs.C031
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C031
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 31) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 31)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3712), (1, 704), (2, 2816), (3, 1472), (4, 1600), (5, 2368), (6, 2618), (7, 1035), (8, 556), (9, 343), (10, 153), (11, 101)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 31) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 31) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 31) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C031
