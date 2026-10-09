import Inputs.C159
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C159
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 159) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 159)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1664), (1, 3776), (2, 3328), (3, 1280), (4, 1920), (5, 2240), (6, 3106), (7, 2611), (8, 3612), (9, 403), (10, 351), (11, 486)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 159) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 159) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 159) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C159
