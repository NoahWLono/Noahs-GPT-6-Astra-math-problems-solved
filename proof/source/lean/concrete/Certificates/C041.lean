import Inputs.C041
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C041
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 41) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 41)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1072), (1, 1576), (2, 2104), (3, 1030), (4, 1541), (5, 2055), (6, 3072), (7, 2560), (8, 3584), (9, 402), (10, 347), (11, 484)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 41) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 41) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 41) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C041
