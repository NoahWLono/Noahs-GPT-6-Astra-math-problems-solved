import Inputs.C163
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C163
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 163) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 163)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 248), (1, 456), (2, 424), (3, 1863), (4, 3713), (5, 3141), (6, 3627), (7, 535), (8, 2574), (9, 472), (10, 120), (11, 368)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 163) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 163) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 163) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C163
