import Inputs.C127
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C127
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 127) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 127)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3848), (1, 928), (2, 2768), (3, 2497), (4, 3140), (5, 1858), (6, 60), (7, 14), (8, 43), (9, 39), (10, 49), (11, 29)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 127) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 127) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 127) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C127
