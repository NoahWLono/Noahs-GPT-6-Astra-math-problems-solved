import Inputs.C226
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C226
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 226) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 226)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 3256), (1, 2760), (2, 3880), (3, 3079), (4, 2561), (5, 3589), (6, 3586), (7, 515), (8, 2564), (9, 502), (10, 109), (11, 383)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 226) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 226) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 226) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C226
