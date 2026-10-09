import Inputs.C236
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C236
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 236) = (-64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 236)) = (-64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1432), (1, 1912), (2, 2544), (3, 3331), (4, 2951), (5, 3782), (6, 1574), (7, 3637), (8, 3103), (9, 242), (10, 491), (11, 444)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 236) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 236) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 236) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C236
