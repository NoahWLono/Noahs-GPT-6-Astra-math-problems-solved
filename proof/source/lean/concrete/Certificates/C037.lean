import Inputs.C037
open FastWalsh QuadraticWalshShift
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace N12.C037
theorem zero_value : componentZeroSum 12 coefficients (BitVec.ofNat 8 37) = (64 : Int) := by
  rw [componentZeroSum_eq_sumTree]
  change sumTree (signTree effective (BitVec.ofNat 8 37)) = (64 : Int)
  rw [input_certificate]
  rfl
def inverseColumns : List (Nat × BitVec 12) := [(0, 48), (1, 40), (2, 56), (3, 1158), (4, 1733), (5, 2311), (6, 3088), (7, 2584), (8, 3616), (9, 400), (10, 344), (11, 480)]
theorem alignment : basisAlignmentCheck coefficients (BitVec.ofNat 8 37) inverseColumns = true := by decide
theorem bent : IsBent effective (BitVec.ofNat 8 37) := by
  apply quadratic_bent_certificate coefficients (BitVec.ofNat 8 37) inverseColumns alignment
  rw [zero_value]
  decide
#print axioms bent
end N12.C037
