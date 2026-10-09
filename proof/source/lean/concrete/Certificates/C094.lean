import Inputs.C094
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C094
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 94) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 94)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3880), (1, 912), (2, 2760), (3, 965), (4, 2114), (5, 1345), (6, 2108), (7, 3086), (8, 1579), (9, 271), (10, 417), (11, 213)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 94) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 94) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 94) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C094
