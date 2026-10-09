import Inputs.C053
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C053
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 53) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 53)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 304), (1, 424), (2, 248), (3, 3206), (4, 2757), (5, 3847), (6, 1044), (7, 1566), (8, 2083), (9, 176), (10, 232), (11, 312)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 53) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 53) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 53) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C053
