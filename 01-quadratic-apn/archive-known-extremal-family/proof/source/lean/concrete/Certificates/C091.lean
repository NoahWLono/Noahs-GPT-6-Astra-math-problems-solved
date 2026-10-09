import Inputs.C091
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C091
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 91) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 91)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 1472), (1, 1600), (2, 2368), (3, 3968), (4, 832), (5, 3008), (6, 1591), (7, 3625), (8, 3133), (9, 250), (10, 459), (11, 428)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 91) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 91) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 91) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C091
