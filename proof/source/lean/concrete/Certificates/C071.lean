import Inputs.C071
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C071
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 71) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 71)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2944), (1, 1344), (2, 960), (3, 3264), (4, 3008), (5, 3968), (6, 30), (7, 61), (8, 55), (9, 53), (10, 42), (11, 57)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 71) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 71) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 71) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C071
