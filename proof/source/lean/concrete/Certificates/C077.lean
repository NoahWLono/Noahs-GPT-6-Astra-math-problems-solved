import Inputs.C077
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C077
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 77) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 77)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 2072), (1, 3128), (2, 1584), (3, 1795), (4, 3975), (5, 3270), (6, 1568), (7, 3632), (8, 3096), (9, 220), (10, 510), (11, 435)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 77) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 77) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 77) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C077
