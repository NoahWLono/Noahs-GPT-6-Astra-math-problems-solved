import Inputs.C096
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C096
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 96) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 96)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1032), (1, 1568), (2, 2064), (3, 129), (4, 196), (5, 258), (6, 528), (7, 2072), (8, 1056), (9, 66), (10, 259), (11, 132)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 96) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 96) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 96) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C096
