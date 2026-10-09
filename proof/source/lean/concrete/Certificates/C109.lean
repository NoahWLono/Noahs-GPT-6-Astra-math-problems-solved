import Inputs.C109
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C109
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 109) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 109)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3616), (1, 560), (2, 2584), (3, 3012), (4, 1094), (5, 835), (6, 2104), (7, 3080), (8, 1576), (9, 303), (10, 401), (11, 205)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 109) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 109) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 109) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C109
